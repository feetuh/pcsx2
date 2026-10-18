// SPDX-FileCopyrightText: 2002-2026 PCSX2 Dev Team
// SPDX-License-Identifier: GPL-3.0+

#include "Achievements.h"
#include "BuildVersion.h"
#include "Common.h"
#include "Counters.h"
#include "DebugTools/Breakpoints.h"
#include "DebugTools/DebugInterface.h"
#include "Host.h"
#include "Elfheader.h"
#include "GS/GS.h"
#include "MTGS.h"
#include "SaveState.h"
#include "PINE.h"
#include "VMManager.h"
#include "vtlb.h"
#include "Recording/InputRecording.h"
#include "Recording/PadData.h"
#include "common/Error.h"
#include "common/FileSystem.h"
#include "common/StringUtil.h"
#include "common/Threading.h"

#include <array>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <memory>
#include <mutex>
#include <optional>
#include <span>
#include <string_view>
#include <sys/types.h>
#include <thread>

#include "fmt/format.h"

#if defined(_WIN32)
#define read_portable(a, b, c) (recv(a, (char*)b, c, 0))
#define write_portable(a, b, c) (send(a, (const char*)b, c, 0))
#define safe_close_portable(a) \
	do \
	{ \
		if ((a) >= 0) \
		{ \
			closesocket((a)); \
			(a) = INVALID_SOCKET; \
		} \
	} while (0)
#include "common/RedtapeWindows.h"
#include <WinSock2.h>
#elif defined(__linux__) || defined(__FreeBSD__)
#define read_portable(a, b, c) (read(a, b, c))
#define write_portable(a, b, c) (send(a, b, c, MSG_NOSIGNAL))
#define safe_close_portable(a) \
	do \
	{ \
		if ((a) >= 0) \
		{ \
			close((a)); \
			(a) = -1; \
		} \
	} while (0)
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#else
#define read_portable(a, b, c) (read(a, b, c))
#define write_portable(a, b, c) (write(a, b, c))
#define safe_close_portable(a) \
	do \
	{ \
		if ((a) >= 0) \
		{ \
			close((a)); \
			(a) = -1; \
		} \
	} while (0)
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#endif

#define PINE_EMULATOR_NAME "pcsx2"

#ifdef _WIN32

static bool InitializeWinsock()
{
	static bool initialized = false;
	if (initialized)
		return true;

	WSADATA wsa = {};
	if (WSAStartup(MAKEWORD(2, 2), &wsa) != 0)
		return false;

	initialized = true;
	std::atexit([]() { WSACleanup(); });
	return true;
}

#endif

namespace PINEServer
{
	static std::thread s_thread;
	static int s_slot;

#ifdef _WIN32
	// windows claim to have support for AF_UNIX sockets but that is a blatant lie,
	// their SDK won't even run their own examples, so we go on TCP sockets.
	static SOCKET s_sock = INVALID_SOCKET;
	// the message socket used in thread's accept().
	static SOCKET s_msgsock = INVALID_SOCKET;
#else
	// absolute path of the socket. Stored in XDG_RUNTIME_DIR, if unset /tmp
	static std::string s_socket_name;
	static int s_sock = -1;
	// the message socket used in thread's accept().
	static int s_msgsock = -1;
#endif

	// Whether the socket processing thread should stop executing/is stopped.
	static std::atomic_bool s_end{true};

	/**
	 * Maximum memory used by an IPC message request.
	 * Equivalent to 50,000 Write64 requests.
	 */
#define MAX_IPC_SIZE 650000

	/**
	 * Maximum memory used by an IPC message reply.
	 * Equivalent to 50,000 Read64 replies.
	 */
#define MAX_IPC_RETURN_SIZE 450000

	/**
	 * IPC return buffer.
	 * A preallocated buffer used to store all IPC replies.
	 * to the size of 50.000 MsgWrite64 IPC calls.
	 */
	static std::vector<u8> s_ret_buffer;

	/**
	 * IPC messages buffer.
	 * A preallocated buffer used to store all IPC messages.
	 */
	static std::vector<u8> s_ipc_buffer;

	/**
	 * IPC Command messages opcodes.
	 * A list of possible operations possible by the IPC.
	 * Each one of them is what we call an "opcode" and is the first
	 * byte sent by the IPC to differentiate between commands.
	 */
	enum IPCCommand : unsigned char
	{
		MsgRead8 = 0, /**< Read 8 bit value to memory. */
		MsgRead16 = 1, /**< Read 16 bit value to memory. */
		MsgRead32 = 2, /**< Read 32 bit value to memory. */
		MsgRead64 = 3, /**< Read 64 bit value to memory. */
		MsgWrite8 = 4, /**< Write 8 bit value to memory. */
		MsgWrite16 = 5, /**< Write 16 bit value to memory. */
		MsgWrite32 = 6, /**< Write 32 bit value to memory. */
		MsgWrite64 = 7, /**< Write 64 bit value to memory. */
		MsgVersion = 8, /**< Returns PCSX2 version. */
		MsgSaveState = 9, /**< Saves a savestate. */
		MsgLoadState = 0xA, /**< Loads a savestate. */
		MsgTitle = 0xB, /**< Returns the game title. */
		MsgID = 0xC, /**< Returns the game ID. */
		MsgUUID = 0xD, /**< Returns the game UUID. */
		MsgGameVersion = 0xE, /**< Returns the game verion. */
		MsgStatus = 0xF, /**< Returns the emulator status. */
		// rust-fm control fork. Private, not for upstream; 0x80-0x9F so we never
		// collide with upstream or other forks. Replies are sent once the work is done.
		MsgForkInfo = 0x80, /**< Returns the fork API version and build. */
		MsgPauseSync = 0x81, /**< Pauses the VM. */
		MsgResumeSync = 0x82, /**< Resumes the VM. */
		MsgFrameAdvanceSync = 0x83, /**< Advances N frames from paused, returns the frame count. */
		MsgFrameInfo = 0x84, /**< Returns frame, VM and input recording state. */
		MsgSetPadFrame = 0x85, /**< Overrides a pad with an 18 byte .p2m frame. */
		MsgClearPadFrame = 0x86, /**< Removes a pad override. */
		MsgRecordingPlay = 0x87, /**< Plays an input recording from paused. */
		MsgRecordingStop = 0x88, /**< Stops the input recording. */
		MsgLoadStateFileSync = 0x89, /**< Loads a savestate file. */
		MsgSaveStateFileSync = 0x8A, /**< Saves a savestate file. */
		MsgEERegisters = 0x90, /**< Returns every EE register category, from paused. */
		MsgAddExecBreakpoint = 0x91, /**< Adds or replaces an EE execute breakpoint. */
		MsgRemoveBreakpoint = 0x92, /**< Removes an EE execute breakpoint. */
		MsgListBreakpoints = 0x93, /**< Lists the EE execute breakpoints. */
		MsgGSDump = 0x94, /**< Queues a screenshot and optional GS dump. */
		MsgUnimplemented = 0xFF /**< Unimplemented IPC message. */
	};

	/**
	 * Fork API version, reported by MsgForkInfo.
	 * Bump it whenever a fork command is added or its wire format changes.
	 */
	static constexpr u32 FORK_API_VERSION = 2;

	/**
	 * Pad overrides set by MsgSetPadFrame, one per port (slot 0 only).
	 * Only touched on the CPU thread.
	 */
	static std::array<std::optional<std::array<u8, 18>>, 2> s_pad_overrides;

	// Most frames MsgFrameAdvanceSync advances in one request (one minute at 60 fps).
	static constexpr u32 MAX_FRAME_ADVANCE = 3600;

	/**
	 * Emulator status enum.
	 * A list of possible emulator statuses.
	 */
	enum EmuStatus : uint32_t
	{
		Running = 0, /**< Game is running */
		Paused = 1, /**< Game is paused */
		Shutdown = 2 /**< Game is shutdown */
	};

	/**
	 * IPC message buffer.
	 * A list of all needed fields to store an IPC message.
	 */
	struct IPCBuffer
	{
		int size; /**< Size of the buffer. */
		std::vector<u8> buffer; /**< Buffer. */
	};

	/**
	 * IPC result codes.
	 * A list of possible result codes the IPC can send back.
	 * Each one of them is what we call an "opcode" or "tag" and is the
	 * first byte sent by the IPC to differentiate between results.
	 */
	enum IPCResult : unsigned char
	{
		IPC_OK = 0, /**< IPC command successfully completed. */
		IPC_FAIL = 0xFF /**< IPC command failed to complete. */
	};

	// Thread used to relay IPC commands.
	void MainLoop();
	void ClientLoop();

	/**
	 * Internal function, Parses an IPC command.
	 * buf: buffer containing the IPC command.
	 * buf_size: size of the buffer announced.
	 * ret_buffer: buffer that will be used to send the reply.
	 * return value: IPCBuffer containing a buffer with the result
	 *               of the command and its size.
	 */
	static IPCBuffer ParseCommand(std::span<u8> buf, std::vector<u8>& ret_buffer, u32 buf_size);

	/**
	 * Formats an IPC buffer
	 * ret_buffer: return buffer to use.
	 * size: size of the IPC buffer.
	 * return value: buffer containing the status code allocated of size
	 */
	static std::vector<u8>& MakeOkIPC(std::vector<u8>& ret_buffer, uint32_t size);
	static std::vector<u8>& MakeFailIPC(std::vector<u8>& ret_buffer, uint32_t size);

	/**
	 * Initializes an open socket for IPC communication.
	 */
	bool AcceptClient();

	/**
	 * Converts a primitive value to bytes in little endian
	 * res_vector: the vector to modify
	 * res: the value to convert
	 * i: where to insert it into the vector
	 * NB: implicitely inlined
	 */
	template <typename T>
	static void ToResultVector(std::vector<u8>& res_vector, T res, int i)
	{
		memcpy(&res_vector[i], (char*)&res, sizeof(T));
	}

	/**
	 * Converts bytes in little endian to a primitive value
	 * span: the span to convert
	 * i: where to load it from the span
	 * return value: the converted value
	 * NB: implicitely inlined
	 */
	template <typename T>
	static T FromSpan(std::span<u8> span, int i)
	{
		return *(T*)(&span[i]);
	}

	/**
	 * Ensures an IPC message isn't too big.
	 * return value: false if checks failed, true otherwise.
	 */
	static inline bool SafetyChecks(u32 command_len, int command_size, u32 reply_len, int reply_size = 0, u32 buf_size = MAX_IPC_SIZE - 1)
	{
		return !((command_len + command_size) > buf_size ||
				 (reply_len + reply_size) >= MAX_IPC_RETURN_SIZE);
	}

	/**
	 * Reads a fork request string: u32 byte length, then that many UTF-8
	 * bytes without a NUL. Advances buf_cnt past it.
	 * return value: false if it doesn't fit in the request or holds a NUL.
	 */
	static bool ReadRequestString(std::span<u8> buf, u32 buf_size, u32& buf_cnt, std::string* out)
	{
		if (!SafetyChecks(buf_cnt, 4, 0, 0, buf_size))
			return false;
		const u32 size = FromSpan<u32>(buf, buf_cnt);
		if (size > buf_size - buf_cnt - 4)
			return false;
		out->assign(reinterpret_cast<const char*>(&buf[buf_cnt + 4]), size);
		if (out->find('\0') != std::string::npos)
			return false;
		buf_cnt += 4 + size;
		return true;
	}

	/**
	 * Size a string takes in a reply, see WriteResultString().
	 */
	static u32 ResultStringSize(std::string_view str)
	{
		return 4 + static_cast<u32>(str.size()) + 1;
	}

	/**
	 * Appends a string to a reply like the stock commands do: u32 size
	 * including the NUL, the bytes, then the NUL. Check the size first.
	 */
	static void WriteResultString(std::vector<u8>& ret_buffer, std::string_view str, u32& ret_cnt)
	{
		ToResultVector<u32>(ret_buffer, static_cast<u32>(str.size()) + 1, ret_cnt);
		std::memcpy(&ret_buffer[ret_cnt + 4], str.data(), str.size());
		ret_buffer[ret_cnt + 4 + str.size()] = 0;
		ret_cnt += ResultStringSize(str);
	}

	/**
	 * Runs a function on the CPU thread and waits for its result.
	 * Host::RunOnCPUThread(fn, true) could deadlock: Deinitialize() runs on
	 * the CPU thread and joins this one. So if the function hasn't started
	 * within start_timeout, or the server is stopping, it's cancelled and
	 * never runs. Once started, we wait for it to finish.
	 * The function must capture by value; it may outlive this call.
	 * return value: the result, or nullopt if cancelled or abandoned.
	 */
	template <typename T>
	static std::optional<T> RunOnCPUThreadAndWait(std::function<T()> func,
		std::chrono::milliseconds start_timeout = std::chrono::seconds(30))
	{
		struct Call
		{
			std::mutex mutex;
			std::condition_variable cv;
			bool started = false;
			bool cancelled = false;
			std::optional<T> result;
		};
		const std::shared_ptr<Call> call = std::make_shared<Call>();

		Host::RunOnCPUThread([call, func = std::move(func)]() {
			{
				std::unique_lock lock(call->mutex);
				if (call->cancelled)
					return;
				call->started = true;
			}
			T result = func();
			{
				std::unique_lock lock(call->mutex);
				call->result = std::move(result);
			}
			call->cv.notify_all();
		});

		const auto deadline = std::chrono::steady_clock::now() + start_timeout;
		std::unique_lock lock(call->mutex);
		while (!call->result.has_value())
		{
			if (s_end.load(std::memory_order_acquire) ||
				(!call->started && std::chrono::steady_clock::now() >= deadline))
			{
				call->cancelled = true;
				return std::nullopt;
			}
			call->cv.wait_for(lock, std::chrono::milliseconds(50));
		}
		return call->result;
	}

	/**
	 * Appends a value to a reply built off this thread, see CopyResult().
	 */
	template <typename T>
	static void AppendResult(std::vector<u8>& out, const T& value)
	{
		const size_t pos = out.size();
		out.resize(pos + sizeof(T));
		std::memcpy(&out[pos], &value, sizeof(T));
	}

	/**
	 * Appends a string to a reply built off this thread, as WriteResultString() does.
	 */
	static void AppendResultString(std::vector<u8>& out, std::string_view str)
	{
		AppendResult<u32>(out, static_cast<u32>(str.size()) + 1);
		out.insert(out.end(), str.begin(), str.end());
		out.push_back(0);
	}

	/**
	 * Copies a reply built off this thread into the return buffer.
	 * return value: false if it doesn't fit.
	 */
	static bool CopyResult(std::vector<u8>& ret_buffer, const std::vector<u8>& data, u32& ret_cnt)
	{
		if (data.size() >= MAX_IPC_RETURN_SIZE || !SafetyChecks(0, 0, ret_cnt, static_cast<int>(data.size())))
			return false;
		std::memcpy(&ret_buffer[ret_cnt], data.data(), data.size());
		ret_cnt += static_cast<u32>(data.size());
		return true;
	}

	/**
	 * Does what the debugger window does when a breakpoint is hit, so resuming
	 * doesn't stop on it again straight away. Nothing happens unless a breakpoint
	 * was hit, and the debugger window may have done it already.
	 * Only call on the CPU thread, before resuming.
	 */
	static void SkipTriggeredBreakpoint()
	{
		if (!CBreakPoints::GetBreakpointTriggered())
			return;

		CBreakPoints::ClearTemporaryBreakPoints();
		CBreakPoints::SetBreakpointTriggered(false, BREAKPOINT_IOP_AND_EE);
		CBreakPoints::SetSkipFirst(BREAKPOINT_EE, r5900Debug.getPC());
		CBreakPoints::SetSkipFirst(BREAKPOINT_IOP, r3000Debug.getPC());
	}

	/**
	 * Waits until a frame advance has paused the VM again.
	 * return value: false on timeout, shutdown, or if the server is stopping.
	 */
	static bool WaitForFrameAdvancePause(u32 frames)
	{
		// Generous, so slow emulation doesn't fail; the VM still pauses if we give up.
		// Needs proper testing with long advances at low emulation speed.
		const auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(10) +
		                      std::chrono::milliseconds(100) * frames;
		while (!s_end.load(std::memory_order_acquire) && std::chrono::steady_clock::now() < deadline)
		{
			switch (VMManager::GetState())
			{
				case VMState::Paused:
					return true;
				case VMState::Running:
				case VMState::Resetting:
					break;
				default:
					return false;
			}
			std::this_thread::sleep_for(std::chrono::milliseconds(1));
		}
		return false;
	}
} // namespace PINEServer

bool PINEServer::Initialize(int slot)
{
	s_end.store(false, std::memory_order_release);
	s_slot = slot;

#ifdef _WIN32
	if (!InitializeWinsock())
	{
		Console.WriteLn(Color_Red, "PINE: Cannot initialize winsock! Shutting down...");
		Deinitialize();
		return false;
	}

	s_sock = socket(AF_INET, SOCK_STREAM, 0);
	if ((s_sock == INVALID_SOCKET) || slot > 65536)
	{
		Console.WriteLn(Color_Red, "PINE: Cannot open socket! Shutting down...");
		Deinitialize();
		return false;
	}

	sockaddr_in server = {};
	server.sin_family = AF_INET;
	server.sin_addr.s_addr = htonl(INADDR_LOOPBACK); // localhost only
	server.sin_port = htons(slot);

	if (bind(s_sock, (struct sockaddr*)&server, sizeof(server)) == SOCKET_ERROR)
	{
		Console.WriteLn(Color_Red, "PINE: Error while binding to socket! Shutting down...");
		Deinitialize();
		return false;
	}

#else
	char* runtime_dir = nullptr;
#ifdef __APPLE__
	runtime_dir = std::getenv("TMPDIR");
#else
	runtime_dir = std::getenv("XDG_RUNTIME_DIR");
#endif
	// fallback in case macOS or other OSes don't implement the XDG base
	// spec
	if (runtime_dir == nullptr)
		s_socket_name = "/tmp/" PINE_EMULATOR_NAME ".sock";
	else
	{
		s_socket_name = runtime_dir;
		s_socket_name += "/" PINE_EMULATOR_NAME ".sock";
	}

	if (slot != PINE_DEFAULT_SLOT)
		s_socket_name += "." + std::to_string(slot);

	struct sockaddr_un server;

	s_sock = socket(AF_UNIX, SOCK_STREAM, 0);
	if (s_sock < 0)
	{
		Console.WriteLn(Color_Red, "PINE: Cannot open socket! Shutting down...");
		Deinitialize();
		return false;
	}
	server.sun_family = AF_UNIX;
	StringUtil::Strlcpy(server.sun_path, s_socket_name, sizeof(server.sun_path));

	// we unlink the socket so that when releasing this thread the socket gets
	// freed even if we didn't close correctly the loop
	unlink(s_socket_name.c_str());
	if (bind(s_sock, (struct sockaddr*)&server, sizeof(struct sockaddr_un)))
	{
		Console.WriteLn(Color_Red, "PINE: Error while binding to socket! Shutting down...");
		Deinitialize();
		return false;
	}
#endif

	// maximum queue of 4096 commands before refusing, approximated to the
	// nearest legal value. We do not use SOMAXCONN as windows have this idea
	// that a "reasonable" value is 5, which is not.
	if (listen(s_sock, 4096))
	{
		Console.WriteLn(Color_Red, "PINE: Cannot listen for connections! Shutting down...");
		Deinitialize();
		return false;
	}

	// we allocate once buffers to not have to do mallocs for each IPC
	// request, as malloc is expansive when we optimize for µs.
	s_ret_buffer.resize(MAX_IPC_RETURN_SIZE);
	s_ipc_buffer.resize(MAX_IPC_SIZE);

	// we start the thread
	s_thread = std::thread(&PINEServer::MainLoop);

	return true;
}

bool PINEServer::IsInitialized()
{
	return !s_end.load(std::memory_order_acquire);
}

int PINEServer::GetSlot()
{
	return s_slot;
}

std::vector<u8>& PINEServer::MakeOkIPC(std::vector<u8>& ret_buffer, uint32_t size = 5)
{
	ToResultVector<uint32_t>(ret_buffer, size, 0);
	ret_buffer[4] = IPC_OK;
	return ret_buffer;
}

std::vector<u8>& PINEServer::MakeFailIPC(std::vector<u8>& ret_buffer, uint32_t size = 5)
{
	ToResultVector<uint32_t>(ret_buffer, size, 0);
	ret_buffer[4] = IPC_FAIL;
	return ret_buffer;
}

bool PINEServer::AcceptClient()
{
	s_msgsock = accept(s_sock, 0, 0);
	if (s_msgsock < 0)
	{
		// everything else is non recoverable in our scope
		// we also mark as recoverable socket errors where it would block a
		// non blocking socket, even though our socket is blocking, in case
		// we ever have to implement a non blocking socket.
#ifdef _WIN32
		const int errno_w = WSAGetLastError();
		if (!(errno_w == WSAECONNRESET || errno_w == WSAEINTR || errno_w == WSAEINPROGRESS || errno_w == WSAEMFILE || errno_w == WSAEWOULDBLOCK) && s_sock != INVALID_SOCKET)
			Console.Error("PINE: accept() returned error %d", errno_w);
#else
		if (!(errno == ECONNABORTED || errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) && s_sock >= 0)
			Console.Error("PINE: accept() returned error %d", errno);
#endif

		return false;
	}

#ifdef __APPLE__
	int nosigpipe = 1;
	setsockopt(s_msgsock, SOL_SOCKET, SO_NOSIGPIPE, &nosigpipe, sizeof(nosigpipe));
#endif

	// Gross C-style cast, but SOCKET is a handle on Windows.
	Console.WriteLn("PINE: New client with FD %d connected.", (int)s_msgsock);
	return true;
}

void PINEServer::MainLoop()
{
	Threading::SetNameOfCurrentThread("PINE Server");

	while (!s_end.load(std::memory_order_acquire))
	{
		if (!AcceptClient())
			continue;

		ClientLoop();

		Console.WriteLn("PINE: Client disconnected.");
		safe_close_portable(s_msgsock);
	}
}

void PINEServer::ClientLoop()
{
	while (!s_end.load(std::memory_order_acquire))
	{
		// either int or ssize_t depending on the platform, so we have to
		// use a bunch of auto
		auto receive_length = 0;
		auto end_length = 4;
		const std::span<u8> ipc_buffer_span(s_ipc_buffer);

		// while we haven't received the entire packet, maybe due to
		// socket datagram splittage, we continue to read
		while (receive_length < end_length)
		{
			const auto tmp_length = read_portable(s_msgsock, &ipc_buffer_span[receive_length], MAX_IPC_SIZE - receive_length);

			// we recreate the socket if an error happens
			if (tmp_length <= 0)
				return;

			receive_length += tmp_length;

			// if we got at least the final size then update
			if (end_length == 4 && receive_length >= 4)
			{
				end_length = FromSpan<u32>(ipc_buffer_span, 0);
				// we'd like to avoid a client trying to do OOB
				if (end_length > MAX_IPC_SIZE || end_length < 4)
				{
					receive_length = 0;
					break;
				}
			}
		}
		PINEServer::IPCBuffer res;

		// we remove 4 bytes to get the message size out of the IPC command
		// size in ParseCommand.
		// also, if we got a failed command, let's reset the state so we don't
		// end up deadlocking by getting out of sync, eg when a client
		// disconnects
		if (receive_length != 0)
		{
			res = ParseCommand(ipc_buffer_span.subspan(4), s_ret_buffer, (u32)end_length - 4);

			// if we cannot send back our answer restart the socket
			if (write_portable(s_msgsock, res.buffer.data(), res.size) < 0)
				return;
		}
	}
}

void PINEServer::Deinitialize()
{
	s_end.store(true, std::memory_order_release);

#ifndef _WIN32
	if (!s_socket_name.empty())
	{
		unlink(s_socket_name.c_str());
		s_socket_name = {};
	}
#endif

	// shutdown() is needed, otherwise accept() will still block.
#ifdef _WIN32
	if (s_sock != INVALID_SOCKET)
		shutdown(s_sock, SD_BOTH);
#else
	if (s_sock >= 0)
		shutdown(s_sock, SHUT_RDWR);
#endif

	safe_close_portable(s_sock);
	safe_close_portable(s_msgsock);

	if (s_thread.joinable())
		s_thread.join();

	// We're on the CPU thread. Pads keep their last state, as with MsgClearPadFrame.
	s_pad_overrides = {};
}

void PINEServer::ApplyPadOverridesOnCPUThread()
{
	// Recordings own the pads while active.
	if (g_InputRecording.isActive())
		return;

	for (u32 port = 0; port < s_pad_overrides.size(); port++)
	{
		if (s_pad_overrides[port].has_value())
			PadData(port, 0, s_pad_overrides[port].value()).OverrideActualController();
	}
}

PINEServer::IPCBuffer PINEServer::ParseCommand(std::span<u8> buf, std::vector<u8>& ret_buffer, u32 buf_size)
{
	u32 ret_cnt = 5;
	u32 buf_cnt = 0;

	while (buf_cnt < buf_size)
	{
		if (!SafetyChecks(buf_cnt, 1, ret_cnt, 0, buf_size)) [[unlikely]]
			return IPCBuffer{5, MakeFailIPC(ret_buffer)};
		buf_cnt++;
		// example IPC messages: MsgRead/Write
		// refer to the client doc for more info on the format
		//         IPC Message event (1 byte)
		//         |  Memory address (4 byte)
		//         |  |           argument (VLE)
		//         |  |           |
		// format: XX YY YY YY YY ZZ ZZ ZZ ZZ
		//        reply code: 00 = OK, FF = NOT OK
		//        |  return value (VLE)
		//        |  |
		// reply: XX ZZ ZZ ZZ ZZ
		switch ((IPCCommand)buf[buf_cnt - 1])
		{
			case MsgRead8:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 1, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				const u8 res = vtlb_ramRead<mem8_t>(a);
				ToResultVector(ret_buffer, res, ret_cnt);
				ret_cnt += 1;
				buf_cnt += 4;
				break;
			}
			case MsgRead16:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 2, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				const u16 res = vtlb_ramRead<mem16_t>(a);
				ToResultVector(ret_buffer, res, ret_cnt);
				ret_cnt += 2;
				buf_cnt += 4;
				break;
			}
			case MsgRead32:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 4, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				const u32 res = vtlb_ramRead<mem32_t>(a);
				ToResultVector(ret_buffer, res, ret_cnt);
				ret_cnt += 4;
				buf_cnt += 4;
				break;
			}
			case MsgRead64:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 8, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				const u64 res = vtlb_ramRead<mem64_t>(a);
				ToResultVector(ret_buffer, res, ret_cnt);
				ret_cnt += 8;
				buf_cnt += 4;
				break;
			}
			case MsgWrite8:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 1 + 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				vtlb_ramWrite<mem8_t>(a, FromSpan<u8>(buf, buf_cnt + 4));
				buf_cnt += 5;
				break;
			}
			case MsgWrite16:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 2 + 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				vtlb_ramWrite<mem16_t>(a, FromSpan<u16>(buf, buf_cnt + 4));
				buf_cnt += 6;
				break;
			}
			case MsgWrite32:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 4 + 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				vtlb_ramWrite<mem32_t>(a, FromSpan<u32>(buf, buf_cnt + 4));
				buf_cnt += 8;
				break;
			}
			case MsgWrite64:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 8 + 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 a = FromSpan<u32>(buf, buf_cnt);
				vtlb_ramWrite<mem64_t>(a, FromSpan<u64>(buf, buf_cnt + 4));
				buf_cnt += 12;
				break;
			}
			case MsgVersion:
			{
				u32 size = strlen(BuildVersion::GitRev) + 7;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, size + 4, buf_size)) [[unlikely]]
					goto error;
				ToResultVector(ret_buffer, size, ret_cnt);
				ret_cnt += 4;
				snprintf(reinterpret_cast<char*>(&ret_buffer[ret_cnt]), size, "PCSX2 %s", BuildVersion::GitRev);
				ret_cnt += size;
				break;
			}
			case MsgSaveState:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 1, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				Host::RunOnCPUThread([slot = FromSpan<u8>(buf, buf_cnt)] {
					VMManager::SaveStateToSlot(slot, true, [slot](const std::string& error) {
						SaveState_ReportSaveErrorOSD(error, slot);
					});
				});
				buf_cnt += 1;
				break;
			}
			case MsgLoadState:
			{
				if (!VMManager::HasValidVM())
					goto error;
				if (!SafetyChecks(buf_cnt, 1, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				Host::RunOnCPUThread([slot = FromSpan<u8>(buf, buf_cnt)] {
					Error state_error;
					if (!VMManager::LoadStateFromSlot(slot, false, &state_error))
						SaveState_ReportLoadErrorOSD(state_error.GetDescription(), slot, false);
				});
				buf_cnt += 1;
				break;
			}
			case MsgTitle:
			{
				if (!VMManager::HasValidVM())
					goto error;
				const std::string gameName = VMManager::GetTitle(false);
				const u32 size = gameName.size() + 1;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, size + 4, buf_size)) [[unlikely]]
					goto error;
				ToResultVector(ret_buffer, size, ret_cnt);
				ret_cnt += 4;
				memcpy(&ret_buffer[ret_cnt], gameName.c_str(), size);
				ret_cnt += size;
				break;
			}
			case MsgID:
			{
				if (!VMManager::HasValidVM())
					goto error;
				const std::string gameSerial = VMManager::GetDiscSerial();
				const u32 size = gameSerial.size() + 1;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, size + 4, buf_size)) [[unlikely]]
					goto error;
				ToResultVector(ret_buffer, size, ret_cnt);
				ret_cnt += 4;
				memcpy(&ret_buffer[ret_cnt], gameSerial.c_str(), size);
				ret_cnt += size;
				break;
			}
			case MsgUUID:
			{
				if (!VMManager::HasValidVM())
					goto error;
				const std::string crc = fmt::format("{:08x}", VMManager::GetDiscCRC());
				const u32 size = crc.size() + 1;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, size + 4, buf_size)) [[unlikely]]
					goto error;
				ToResultVector(ret_buffer, size, ret_cnt);
				ret_cnt += 4;
				memcpy(&ret_buffer[ret_cnt], crc.c_str(), size);
				ret_cnt += size;
				break;
			}
			case MsgGameVersion:
			{
				if (!VMManager::HasValidVM())
					goto error;

				const std::string ElfVersion = VMManager::GetDiscVersion();
				const u32 size = ElfVersion.size() + 1;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, size + 4, buf_size)) [[unlikely]]
					goto error;
				ToResultVector(ret_buffer, size, ret_cnt);
				ret_cnt += 4;
				memcpy(&ret_buffer[ret_cnt], ElfVersion.c_str(), size);
				ret_cnt += size;
				break;
			}
			case MsgStatus:
			{
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, 4, buf_size)) [[unlikely]]
					goto error;
				EmuStatus status;

				switch (VMManager::GetState())
				{
					case VMState::Running:
						status = EmuStatus::Running;
						break;
					case VMState::Paused:
						status = EmuStatus::Paused;
						break;
					default:
						status = EmuStatus::Shutdown;
						break;
				}

				ToResultVector(ret_buffer, status, ret_cnt);
				ret_cnt += 4;
				break;
			}
			case MsgForkInfo:
			{
				const std::string_view rev = BuildVersion::GitRev;
				const std::string_view hash = BuildVersion::GitHash;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, 4 + ResultStringSize(rev) + ResultStringSize(hash), buf_size)) [[unlikely]]
					goto error;
				ToResultVector<u32>(ret_buffer, FORK_API_VERSION, ret_cnt);
				ret_cnt += 4;
				WriteResultString(ret_buffer, rev, ret_cnt);
				WriteResultString(ret_buffer, hash, ret_cnt);
				break;
			}
			case MsgPauseSync:
			{
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				const std::optional<bool> paused = RunOnCPUThreadAndWait<bool>([]() {
					if (VMManager::GetState() == VMState::Running)
						VMManager::SetPaused(true);
					return VMManager::GetState() == VMState::Paused;
				});
				if (!paused.value_or(false))
					goto error;
				break;
			}
			case MsgResumeSync:
			{
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				const std::optional<bool> running = RunOnCPUThreadAndWait<bool>([]() {
					if (VMManager::GetState() == VMState::Paused)
					{
						SkipTriggeredBreakpoint();
						VMManager::SetPaused(false);
					}
					return VMManager::GetState() == VMState::Running;
				});
				if (!running.value_or(false))
					goto error;
				break;
			}
			case MsgFrameAdvanceSync:
			{
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 4, buf_size)) [[unlikely]]
					goto error;
				const u32 frames = FromSpan<u32>(buf, buf_cnt);
				buf_cnt += 4;
				if (frames < 1 || frames > MAX_FRAME_ADVANCE)
					goto error;
				// Same call as the frame advance hotkey, so stepping matches it.
				const std::optional<bool> started = RunOnCPUThreadAndWait<bool>([frames]() {
					if (VMManager::GetState() != VMState::Paused)
						return false;
					SkipTriggeredBreakpoint();
					VMManager::FrameAdvance(frames);
					return VMManager::GetState() == VMState::Running;
				});
				if (!started.value_or(false) || !WaitForFrameAdvancePause(frames))
					goto error;
				// Read on the CPU thread, which is back in its paused loop by now.
				const std::optional<u32> frame = RunOnCPUThreadAndWait<u32>([]() { return g_FrameCount; });
				if (!frame.has_value())
					goto error;
				ToResultVector<u32>(ret_buffer, frame.value(), ret_cnt);
				ret_cnt += 4;
				break;
			}
			case MsgFrameInfo:
			{
				if (Achievements::IsHardcoreModeActive())
					goto error;
				if (!SafetyChecks(buf_cnt, 0, ret_cnt, 16, buf_size)) [[unlikely]]
					goto error;
				const std::optional<std::array<u8, 16>> info = RunOnCPUThreadAndWait<std::array<u8, 16>>([]() {
					std::array<u8, 16> data = {};
					const bool active = g_InputRecording.isActive();
					const u32 frame = g_FrameCount;
					const u32 rec_frame = active ? g_InputRecording.getFrameCounter() : 0;
					const u32 rec_total = active ? g_InputRecording.getData().getTotalFrames() : 0;
					std::memcpy(&data[0], &frame, sizeof(frame));
					data[4] = static_cast<u8>(VMManager::GetState());
					data[5] = active;
					data[6] = active && g_InputRecording.getControls().isRecording();
					std::memcpy(&data[7], &rec_frame, sizeof(rec_frame));
					std::memcpy(&data[11], &rec_total, sizeof(rec_total));
					for (u32 port = 0; port < s_pad_overrides.size(); port++)
						data[15] |= static_cast<u8>(s_pad_overrides[port].has_value() << port);
					return data;
				});
				if (!info.has_value())
					goto error;
				std::memcpy(&ret_buffer[ret_cnt], info->data(), info->size());
				ret_cnt += info->size();
				break;
			}
			case MsgSetPadFrame:
			{
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				if (!SafetyChecks(buf_cnt, 1 + 18, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u8 port = FromSpan<u8>(buf, buf_cnt);
				std::array<u8, 18> frame;
				std::memcpy(frame.data(), &buf[buf_cnt + 1], frame.size());
				buf_cnt += 1 + 18;
				if (port >= s_pad_overrides.size())
					goto error;
				const std::optional<bool> set = RunOnCPUThreadAndWait<bool>([port, frame]() {
					if (g_InputRecording.isActive())
						return false;
					// Apply now as well: when paused, the next input poll comes after the
					// game has already read its pad for the next frame. Held keys apply
					// immediately too, so stepping this way matches keyboard stepping.
					s_pad_overrides[port] = frame;
					PadData(port, 0, frame).OverrideActualController();
					return true;
				});
				if (!set.value_or(false))
					goto error;
				break;
			}
			case MsgClearPadFrame:
			{
				if (Achievements::IsHardcoreModeActive())
					goto error;
				if (!SafetyChecks(buf_cnt, 1, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				// Port 0xFF clears every port.
				const u8 port = FromSpan<u8>(buf, buf_cnt);
				buf_cnt += 1;
				if (port >= s_pad_overrides.size() && port != 0xFF)
					goto error;
				const std::optional<bool> cleared = RunOnCPUThreadAndWait<bool>([port]() {
					if (port == 0xFF)
						s_pad_overrides = {};
					else
						s_pad_overrides[port].reset();
					return true;
				});
				if (!cleared.has_value())
					goto error;
				break;
			}
			case MsgRecordingPlay:
			{
				std::string path;
				if (!ReadRequestString(buf, buf_size, buf_cnt, &path) || path.empty())
					goto error;
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				// Mirrors MainWindow::onInputRecPlayActionTriggered(), minus the dialog.
				const std::optional<bool> playing = RunOnCPUThreadAndWait<bool>([path]() {
					if (!EmuConfig.EnableRecordingTools)
					{
						Console.Error("PINE: Input recording tools are disabled.");
						return false;
					}
					if (VMManager::GetState() != VMState::Paused)
						return false;
					if (g_InputRecording.isActive())
						g_InputRecording.stop();
					if (g_InputRecording.isActive())
						return false;
					s_pad_overrides = {};
					return g_InputRecording.play(path);
				});
				if (!playing.value_or(false))
					goto error;
				break;
			}
			case MsgRecordingStop:
			{
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				// Closes now when paused, otherwise at the end of the current frame.
				const std::optional<bool> stopped = RunOnCPUThreadAndWait<bool>([]() {
					g_InputRecording.stop();
					return true;
				});
				if (!stopped.has_value())
					goto error;
				break;
			}
			case MsgLoadStateFileSync:
			{
				std::string path;
				if (!ReadRequestString(buf, buf_size, buf_cnt, &path) || path.empty())
					goto error;
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				const std::optional<bool> loaded = RunOnCPUThreadAndWait<bool>([path]() {
					// LoadState() resets the VM on failure, so don't let a bad path get that far.
					if (!FileSystem::FileExists(path.c_str()))
					{
						Console.Error(fmt::format("PINE: Savestate '{}' does not exist.", path));
						return false;
					}
					Error load_error;
					if (!VMManager::LoadState(path.c_str(), &load_error))
					{
						Console.Error(fmt::format("PINE: Failed to load '{}': {}", path, load_error.GetDescription()));
						return false;
					}
					return true;
				});
				if (!loaded.value_or(false))
					goto error;
				break;
			}
			case MsgSaveStateFileSync:
			{
				std::string path;
				if (!ReadRequestString(buf, buf_size, buf_cnt, &path) || path.empty())
					goto error;
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				const std::optional<bool> saved = RunOnCPUThreadAndWait<bool>([path]() {
					std::string save_error;
					VMManager::SaveState(path.c_str(), false, false, [&save_error](const std::string& error) {
						save_error = error.empty() ? std::string("unknown error") : error;
					});
					VMManager::WaitForSaveStateFlush();
					if (!save_error.empty())
					{
						Console.Error(fmt::format("PINE: Failed to save '{}': {}", path, save_error));
						return false;
					}
					return true;
				});
				if (!saved.value_or(false))
					goto error;
				break;
			}
			case MsgEERegisters:
			{
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				// Uses the generic debugger categories, so new registers show up by themselves.
				const std::optional<std::vector<u8>> regs = RunOnCPUThreadAndWait<std::vector<u8>>([]() {
					std::vector<u8> data;
					if (VMManager::GetState() != VMState::Paused)
						return data;
					AppendResult<u32>(data, r5900Debug.getPC());
					const int categories = r5900Debug.getRegisterCategoryCount();
					AppendResult<u8>(data, static_cast<u8>(categories));
					for (int cat = 0; cat < categories; cat++)
					{
						const int count = r5900Debug.getRegisterCount(cat);
						AppendResult<u8>(data, static_cast<u8>(cat));
						AppendResultString(data, r5900Debug.getRegisterCategoryName(cat));
						AppendResult<u16>(data, static_cast<u16>(count));
						AppendResult<u8>(data, static_cast<u8>(r5900Debug.getRegisterSize(cat) / 8));
						for (int num = 0; num < count; num++)
						{
							AppendResultString(data, r5900Debug.getRegisterName(cat, num));
							AppendResult<u128>(data, r5900Debug.getRegister(cat, num));
						}
					}
					return data;
				});
				if (!regs.has_value() || regs->empty() || !CopyResult(ret_buffer, regs.value(), ret_cnt))
					goto error;
				break;
			}
			case MsgAddExecBreakpoint:
			{
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 addr = FromSpan<u32>(buf, buf_cnt);
				buf_cnt += 4;
				std::string condition, description;
				if (!ReadRequestString(buf, buf_size, buf_cnt, &condition) ||
					!ReadRequestString(buf, buf_size, buf_cnt, &description))
				{
					goto error;
				}
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				// Mirrors BreakpointModel: parse the condition, then add on the CPU thread.
				// Requires paused, so CBreakPoints::Update() doesn't pause and resume the VM itself.
				const std::optional<bool> added = RunOnCPUThreadAndWait<bool>([addr, condition, description]() {
					if (VMManager::GetState() != VMState::Paused)
						return false;
					BreakPointCond cond;
					if (!condition.empty())
					{
						std::string expr_error;
						if (!r5900Debug.initExpression(condition.c_str(), cond.expression, expr_error))
						{
							Console.Error(fmt::format("PINE: Invalid breakpoint condition '{}': {}", condition, expr_error));
							return false;
						}
						cond.debug = &r5900Debug;
						cond.expressionString = condition;
					}
					if (CBreakPoints::IsAddressBreakPoint(BREAKPOINT_EE, addr))
						CBreakPoints::RemoveBreakPoint(BREAKPOINT_EE, addr);
					CBreakPoints::AddBreakPoint(BREAKPOINT_EE, addr);
					CBreakPoints::ChangeBreakPointDescription(BREAKPOINT_EE, addr, description);
					if (!condition.empty())
						CBreakPoints::ChangeBreakPointAddCond(BREAKPOINT_EE, addr, cond);
					return true;
				});
				if (!added.value_or(false))
					goto error;
				break;
			}
			case MsgRemoveBreakpoint:
			{
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 addr = FromSpan<u32>(buf, buf_cnt);
				buf_cnt += 4;
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				const std::optional<bool> removed = RunOnCPUThreadAndWait<bool>([addr]() {
					if (VMManager::GetState() != VMState::Paused || !CBreakPoints::IsAddressBreakPoint(BREAKPOINT_EE, addr))
						return false;
					CBreakPoints::RemoveBreakPoint(BREAKPOINT_EE, addr);
					return true;
				});
				if (!removed.value_or(false))
					goto error;
				break;
			}
			case MsgListBreakpoints:
			{
				if (Achievements::IsHardcoreModeActive())
					goto error;
				const std::optional<std::vector<u8>> list = RunOnCPUThreadAndWait<std::vector<u8>>([]() {
					const std::vector<BreakPoint> breakpoints = CBreakPoints::GetBreakpoints(BREAKPOINT_EE, false);
					std::vector<u8> data;
					AppendResult<u32>(data, static_cast<u32>(breakpoints.size()));
					for (const BreakPoint& bp : breakpoints)
					{
						AppendResult<u32>(data, bp.addr);
						AppendResult<u8>(data, bp.enabled);
						AppendResultString(data, bp.hasCond ? std::string_view(bp.cond.expressionString) : std::string_view());
						AppendResultString(data, bp.description);
					}
					return data;
				});
				if (!list.has_value() || !CopyResult(ret_buffer, list.value(), ret_cnt))
					goto error;
				break;
			}
			case MsgGSDump:
			{
				std::string path;
				if (!ReadRequestString(buf, buf_size, buf_cnt, &path))
					goto error;
				if (!SafetyChecks(buf_cnt, 4, ret_cnt, 0, buf_size)) [[unlikely]]
					goto error;
				const u32 frames = FromSpan<u32>(buf, buf_cnt);
				buf_cnt += 4;
				// The renderer only takes a full path ending in .png, otherwise it silently
				// picks its own name. Empty means its own name in the snapshots folder.
				if (!path.empty() && !StringUtil::EndsWithNoCase(path, ".png"))
					goto error;
				if (!VMManager::HasValidVM() || Achievements::IsHardcoreModeActive())
					goto error;
				// Same as Tools > Save Single Frame GS Dump; written at the next presented frame.
				const std::optional<bool> queued = RunOnCPUThreadAndWait<bool>([path, frames]() {
					MTGS::RunOnGSThread([path, frames]() { GSQueueSnapshot(path, frames); });
					return true;
				});
				if (!queued.has_value())
					goto error;
				break;
			}
			default:
			{
			error:
				return IPCBuffer{5, MakeFailIPC(ret_buffer)};
			}
		}
	}
	return IPCBuffer{(int)ret_cnt, MakeOkIPC(ret_buffer, ret_cnt)};
}
