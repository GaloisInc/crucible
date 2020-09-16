use crate::fmt;
use crate::io::{self, Error, ErrorKind};
use crate::net::{Ipv4Addr, Ipv6Addr, SocketAddr, ToSocketAddrs};
use crate::sys_common::net as net_imp;
use crate::sys_common::{AsInner, FromInner, IntoInner};
use crate::time::Duration;

/// A UDP socket.
///
/// After creating a `UdpSocket` by [`bind`]ing it to a socket address, data can be
/// [sent to] and [received from] any other socket address.
///
/// Although UDP is a connectionless protocol, this implementation provides an interface
/// to set an address where data should be sent and received from. After setting a remote
/// address with [`connect`], data can be sent to and received from that address with
/// [`send`] and [`recv`].
///
/// As stated in the User Datagram Protocol's specification in [IETF RFC 768], UDP is
/// an unordered, unreliable protocol; refer to [`TcpListener`] and [`TcpStream`] for TCP
/// primitives.
///
/// [`bind`]: #method.bind
/// [`connect`]: #method.connect
/// [IETF RFC 768]: https://tools.ietf.org/html/rfc768
/// [`recv`]: #method.recv
/// [received from]: #method.recv_from
/// [`send`]: #method.send
/// [sent to]: #method.send_to
/// [`TcpListener`]: ../../std/net/struct.TcpListener.html
/// [`TcpStream`]: ../../std/net/struct.TcpStream.html
///
/// # Examples
///
/// ```no_run
/// use std::net::UdpSocket;
///
/// fn main() -> std::io::Result<()> {
///     {
///         let mut socket = UdpSocket::bind("127.0.0.1:34254")?;
///
///         // Receives a single datagram message on the socket. If `buf` is too small to hold
///         // the message, it will be cut off.
///         let mut buf = [0; 10];
///         let (amt, src) = socket.recv_from(&mut buf)?;
///
///         // Redeclare `buf` as slice of the received data and send reverse data back to origin.
///         let buf = &mut buf[..amt];
///         buf.reverse();
///         socket.send_to(buf, &src)?;
///     } // the socket is closed here
///     Ok(())
/// }
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub struct UdpSocket(net_imp::UdpSocket);

impl UdpSocket {
    /// Creates a UDP socket from the given address.
    ///
    /// The address type can be any implementor of [`ToSocketAddrs`] trait. See
    /// its documentation for concrete examples.
    ///
    /// If `addr` yields multiple addresses, `bind` will be attempted with
    /// each of the addresses until one succeeds and returns the socket. If none
    /// of the addresses succeed in creating a socket, the error returned from
    /// the last attempt (the last address) is returned.
    ///
    /// [`ToSocketAddrs`]: ../../std/net/trait.ToSocketAddrs.html
    ///
    /// # Examples
    ///
    /// Creates a UDP socket bound to `127.0.0.1:3400`:
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:3400").expect("couldn't bind to address");
    /// ```
    ///
    /// Creates a UDP socket bound to `127.0.0.1:3400`. If the socket cannot be
    /// bound to that address, create a UDP socket bound to `127.0.0.1:3401`:
    ///
    /// ```no_run
    /// use std::net::{SocketAddr, UdpSocket};
    ///
    /// let addrs = [
    ///     SocketAddr::from(([127, 0, 0, 1], 3400)),
    ///     SocketAddr::from(([127, 0, 0, 1], 3401)),
    /// ];
    /// let socket = UdpSocket::bind(&addrs[..]).expect("couldn't bind to address");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn bind<A: ToSocketAddrs>(addr: A) -> io::Result<UdpSocket> {
        super::each_addr(addr, net_imp::UdpSocket::bind).map(UdpSocket)
    }

    /// Receives a single datagram message on the socket. On success, returns the number
    /// of bytes read and the origin.
    ///
    /// The function must be called with valid byte array `buf` of sufficient size to
    /// hold the message bytes. If a message is too long to fit in the supplied buffer,
    /// excess bytes may be discarded.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// let mut buf = [0; 10];
    /// let (number_of_bytes, src_addr) = socket.recv_from(&mut buf)
    ///                                         .expect("Didn't receive data");
    /// let filled_buf = &mut buf[..number_of_bytes];
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn recv_from(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr)> {
        self.0.recv_from(buf)
    }

    /// Receives a single datagram message on the socket, without removing it from the
    /// queue. On success, returns the number of bytes read and the origin.
    ///
    /// The function must be called with valid byte array `buf` of sufficient size to
    /// hold the message bytes. If a message is too long to fit in the supplied buffer,
    /// excess bytes may be discarded.
    ///
    /// Successive calls return the same data. This is accomplished by passing
    /// `MSG_PEEK` as a flag to the underlying `recvfrom` system call.
    ///
    /// Do not use this function to implement busy waiting, instead use `libc::poll` to
    /// synchronize IO events on one or more sockets.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// let mut buf = [0; 10];
    /// let (number_of_bytes, src_addr) = socket.peek_from(&mut buf)
    ///                                         .expect("Didn't receive data");
    /// let filled_buf = &mut buf[..number_of_bytes];
    /// ```
    #[stable(feature = "peek", since = "1.18.0")]
    pub fn peek_from(&self, buf: &mut [u8]) -> io::Result<(usize, SocketAddr)> {
        self.0.peek_from(buf)
    }

    /// Sends data on the socket to the given address. On success, returns the
    /// number of bytes written.
    ///
    /// Address type can be any implementor of [`ToSocketAddrs`] trait. See its
    /// documentation for concrete examples.
    ///
    /// It is possible for `addr` to yield multiple addresses, but `send_to`
    /// will only send data to the first address yielded by `addr`.
    ///
    /// This will return an error when the IP version of the local socket
    /// does not match that returned from [`ToSocketAddrs`].
    ///
    /// See issue #34202 for more details.
    ///
    /// [`ToSocketAddrs`]: ../../std/net/trait.ToSocketAddrs.html
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.send_to(&[0; 10], "127.0.0.1:4242").expect("couldn't send data");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn send_to<A: ToSocketAddrs>(&self, buf: &[u8], addr: A) -> io::Result<usize> {
        match addr.to_socket_addrs()?.next() {
            Some(addr) => self.0.send_to(buf, &addr),
            None => Err(Error::new(ErrorKind::InvalidInput, "no addresses to send data to")),
        }
    }

    /// Returns the socket address of the remote peer this socket was connected to.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket};
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.connect("192.168.0.1:41203").expect("couldn't connect to address");
    /// assert_eq!(socket.peer_addr().unwrap(),
    ///            SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(192, 168, 0, 1), 41203)));
    /// ```
    ///
    /// If the socket isn't connected, it will return a [`NotConnected`] error.
    ///
    /// [`NotConnected`]: ../../std/io/enum.ErrorKind.html#variant.NotConnected
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// assert_eq!(socket.peer_addr().unwrap_err().kind(),
    ///            std::io::ErrorKind::NotConnected);
    /// ```
    #[stable(feature = "udp_peer_addr", since = "1.40.0")]
    pub fn peer_addr(&self) -> io::Result<SocketAddr> {
        self.0.peer_addr()
    }

    /// Returns the socket address that this socket was created from.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4, UdpSocket};
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// assert_eq!(socket.local_addr().unwrap(),
    ///            SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 34254)));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.0.socket_addr()
    }

    /// Creates a new independently owned handle to the underlying socket.
    ///
    /// The returned `UdpSocket` is a reference to the same socket that this
    /// object references. Both handles will read and write the same port, and
    /// options set on one socket will be propagated to the other.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// let socket_clone = socket.try_clone().expect("couldn't clone the socket");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn try_clone(&self) -> io::Result<UdpSocket> {
        self.0.duplicate().map(UdpSocket)
    }

    /// Sets the read timeout to the timeout specified.
    ///
    /// If the value specified is [`None`], then [`read`] calls will block
    /// indefinitely. An [`Err`] is returned if the zero [`Duration`] is
    /// passed to this method.
    ///
    /// # Platform-specific behavior
    ///
    /// Platforms may return a different error code whenever a read times out as
    /// a result of setting this option. For example Unix typically returns an
    /// error of the kind [`WouldBlock`], but Windows may return [`TimedOut`].
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    /// [`Err`]: ../../std/result/enum.Result.html#variant.Err
    /// [`read`]: ../../std/io/trait.Read.html#tymethod.read
    /// [`Duration`]: ../../std/time/struct.Duration.html
    /// [`WouldBlock`]: ../../std/io/enum.ErrorKind.html#variant.WouldBlock
    /// [`TimedOut`]: ../../std/io/enum.ErrorKind.html#variant.TimedOut
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_read_timeout(None).expect("set_read_timeout call failed");
    /// ```
    ///
    /// An [`Err`] is returned if the zero [`Duration`] is passed to this
    /// method:
    ///
    /// ```no_run
    /// use std::io;
    /// use std::net::UdpSocket;
    /// use std::time::Duration;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").unwrap();
    /// let result = socket.set_read_timeout(Some(Duration::new(0, 0)));
    /// let err = result.unwrap_err();
    /// assert_eq!(err.kind(), io::ErrorKind::InvalidInput)
    /// ```
    #[stable(feature = "socket_timeout", since = "1.4.0")]
    pub fn set_read_timeout(&self, dur: Option<Duration>) -> io::Result<()> {
        self.0.set_read_timeout(dur)
    }

    /// Sets the write timeout to the timeout specified.
    ///
    /// If the value specified is [`None`], then [`write`] calls will block
    /// indefinitely. An [`Err`] is returned if the zero [`Duration`] is
    /// passed to this method.
    ///
    /// # Platform-specific behavior
    ///
    /// Platforms may return a different error code whenever a write times out
    /// as a result of setting this option. For example Unix typically returns
    /// an error of the kind [`WouldBlock`], but Windows may return [`TimedOut`].
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    /// [`Err`]: ../../std/result/enum.Result.html#variant.Err
    /// [`write`]: ../../std/io/trait.Write.html#tymethod.write
    /// [`Duration`]: ../../std/time/struct.Duration.html
    /// [`WouldBlock`]: ../../std/io/enum.ErrorKind.html#variant.WouldBlock
    /// [`TimedOut`]: ../../std/io/enum.ErrorKind.html#variant.TimedOut
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_write_timeout(None).expect("set_write_timeout call failed");
    /// ```
    ///
    /// An [`Err`] is returned if the zero [`Duration`] is passed to this
    /// method:
    ///
    /// ```no_run
    /// use std::io;
    /// use std::net::UdpSocket;
    /// use std::time::Duration;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").unwrap();
    /// let result = socket.set_write_timeout(Some(Duration::new(0, 0)));
    /// let err = result.unwrap_err();
    /// assert_eq!(err.kind(), io::ErrorKind::InvalidInput)
    /// ```
    #[stable(feature = "socket_timeout", since = "1.4.0")]
    pub fn set_write_timeout(&self, dur: Option<Duration>) -> io::Result<()> {
        self.0.set_write_timeout(dur)
    }

    /// Returns the read timeout of this socket.
    ///
    /// If the timeout is [`None`], then [`read`] calls will block indefinitely.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    /// [`read`]: ../../std/io/trait.Read.html#tymethod.read
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_read_timeout(None).expect("set_read_timeout call failed");
    /// assert_eq!(socket.read_timeout().unwrap(), None);
    /// ```
    #[stable(feature = "socket_timeout", since = "1.4.0")]
    pub fn read_timeout(&self) -> io::Result<Option<Duration>> {
        self.0.read_timeout()
    }

    /// Returns the write timeout of this socket.
    ///
    /// If the timeout is [`None`], then [`write`] calls will block indefinitely.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    /// [`write`]: ../../std/io/trait.Write.html#tymethod.write
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_write_timeout(None).expect("set_write_timeout call failed");
    /// assert_eq!(socket.write_timeout().unwrap(), None);
    /// ```
    #[stable(feature = "socket_timeout", since = "1.4.0")]
    pub fn write_timeout(&self) -> io::Result<Option<Duration>> {
        self.0.write_timeout()
    }

    /// Sets the value of the `SO_BROADCAST` option for this socket.
    ///
    /// When enabled, this socket is allowed to send packets to a broadcast
    /// address.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_broadcast(false).expect("set_broadcast call failed");
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn set_broadcast(&self, broadcast: bool) -> io::Result<()> {
        self.0.set_broadcast(broadcast)
    }

    /// Gets the value of the `SO_BROADCAST` option for this socket.
    ///
    /// For more information about this option, see
    /// [`set_broadcast`][link].
    ///
    /// [link]: #method.set_broadcast
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_broadcast(false).expect("set_broadcast call failed");
    /// assert_eq!(socket.broadcast().unwrap(), false);
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn broadcast(&self) -> io::Result<bool> {
        self.0.broadcast()
    }

    /// Sets the value of the `IP_MULTICAST_LOOP` option for this socket.
    ///
    /// If enabled, multicast packets will be looped back to the local socket.
    /// Note that this may not have any effect on IPv6 sockets.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_multicast_loop_v4(false).expect("set_multicast_loop_v4 call failed");
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn set_multicast_loop_v4(&self, multicast_loop_v4: bool) -> io::Result<()> {
        self.0.set_multicast_loop_v4(multicast_loop_v4)
    }

    /// Gets the value of the `IP_MULTICAST_LOOP` option for this socket.
    ///
    /// For more information about this option, see
    /// [`set_multicast_loop_v4`][link].
    ///
    /// [link]: #method.set_multicast_loop_v4
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_multicast_loop_v4(false).expect("set_multicast_loop_v4 call failed");
    /// assert_eq!(socket.multicast_loop_v4().unwrap(), false);
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn multicast_loop_v4(&self) -> io::Result<bool> {
        self.0.multicast_loop_v4()
    }

    /// Sets the value of the `IP_MULTICAST_TTL` option for this socket.
    ///
    /// Indicates the time-to-live value of outgoing multicast packets for
    /// this socket. The default value is 1 which means that multicast packets
    /// don't leave the local network unless explicitly requested.
    ///
    /// Note that this may not have any effect on IPv6 sockets.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_multicast_ttl_v4(42).expect("set_multicast_ttl_v4 call failed");
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn set_multicast_ttl_v4(&self, multicast_ttl_v4: u32) -> io::Result<()> {
        self.0.set_multicast_ttl_v4(multicast_ttl_v4)
    }

    /// Gets the value of the `IP_MULTICAST_TTL` option for this socket.
    ///
    /// For more information about this option, see
    /// [`set_multicast_ttl_v4`][link].
    ///
    /// [link]: #method.set_multicast_ttl_v4
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_multicast_ttl_v4(42).expect("set_multicast_ttl_v4 call failed");
    /// assert_eq!(socket.multicast_ttl_v4().unwrap(), 42);
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn multicast_ttl_v4(&self) -> io::Result<u32> {
        self.0.multicast_ttl_v4()
    }

    /// Sets the value of the `IPV6_MULTICAST_LOOP` option for this socket.
    ///
    /// Controls whether this socket sees the multicast packets it sends itself.
    /// Note that this may not have any affect on IPv4 sockets.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_multicast_loop_v6(false).expect("set_multicast_loop_v6 call failed");
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn set_multicast_loop_v6(&self, multicast_loop_v6: bool) -> io::Result<()> {
        self.0.set_multicast_loop_v6(multicast_loop_v6)
    }

    /// Gets the value of the `IPV6_MULTICAST_LOOP` option for this socket.
    ///
    /// For more information about this option, see
    /// [`set_multicast_loop_v6`][link].
    ///
    /// [link]: #method.set_multicast_loop_v6
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_multicast_loop_v6(false).expect("set_multicast_loop_v6 call failed");
    /// assert_eq!(socket.multicast_loop_v6().unwrap(), false);
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn multicast_loop_v6(&self) -> io::Result<bool> {
        self.0.multicast_loop_v6()
    }

    /// Sets the value for the `IP_TTL` option on this socket.
    ///
    /// This value sets the time-to-live field that is used in every packet sent
    /// from this socket.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_ttl(42).expect("set_ttl call failed");
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn set_ttl(&self, ttl: u32) -> io::Result<()> {
        self.0.set_ttl(ttl)
    }

    /// Gets the value of the `IP_TTL` option for this socket.
    ///
    /// For more information about this option, see [`set_ttl`][link].
    ///
    /// [link]: #method.set_ttl
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.set_ttl(42).expect("set_ttl call failed");
    /// assert_eq!(socket.ttl().unwrap(), 42);
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn ttl(&self) -> io::Result<u32> {
        self.0.ttl()
    }

    /// Executes an operation of the `IP_ADD_MEMBERSHIP` type.
    ///
    /// This function specifies a new multicast group for this socket to join.
    /// The address must be a valid multicast address, and `interface` is the
    /// address of the local interface with which the system should join the
    /// multicast group. If it's equal to `INADDR_ANY` then an appropriate
    /// interface is chosen by the system.
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn join_multicast_v4(&self, multiaddr: &Ipv4Addr, interface: &Ipv4Addr) -> io::Result<()> {
        self.0.join_multicast_v4(multiaddr, interface)
    }

    /// Executes an operation of the `IPV6_ADD_MEMBERSHIP` type.
    ///
    /// This function specifies a new multicast group for this socket to join.
    /// The address must be a valid multicast address, and `interface` is the
    /// index of the interface to join/leave (or 0 to indicate any interface).
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn join_multicast_v6(&self, multiaddr: &Ipv6Addr, interface: u32) -> io::Result<()> {
        self.0.join_multicast_v6(multiaddr, interface)
    }

    /// Executes an operation of the `IP_DROP_MEMBERSHIP` type.
    ///
    /// For more information about this option, see
    /// [`join_multicast_v4`][link].
    ///
    /// [link]: #method.join_multicast_v4
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn leave_multicast_v4(&self, multiaddr: &Ipv4Addr, interface: &Ipv4Addr) -> io::Result<()> {
        self.0.leave_multicast_v4(multiaddr, interface)
    }

    /// Executes an operation of the `IPV6_DROP_MEMBERSHIP` type.
    ///
    /// For more information about this option, see
    /// [`join_multicast_v6`][link].
    ///
    /// [link]: #method.join_multicast_v6
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn leave_multicast_v6(&self, multiaddr: &Ipv6Addr, interface: u32) -> io::Result<()> {
        self.0.leave_multicast_v6(multiaddr, interface)
    }

    /// Gets the value of the `SO_ERROR` option on this socket.
    ///
    /// This will retrieve the stored error in the underlying socket, clearing
    /// the field in the process. This can be useful for checking errors between
    /// calls.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// match socket.take_error() {
    ///     Ok(Some(error)) => println!("UdpSocket error: {:?}", error),
    ///     Ok(None) => println!("No error"),
    ///     Err(error) => println!("UdpSocket.take_error failed: {:?}", error),
    /// }
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn take_error(&self) -> io::Result<Option<io::Error>> {
        self.0.take_error()
    }

    /// Connects this UDP socket to a remote address, allowing the `send` and
    /// `recv` syscalls to be used to send data and also applies filters to only
    /// receive data from the specified address.
    ///
    /// If `addr` yields multiple addresses, `connect` will be attempted with
    /// each of the addresses until the underlying OS function returns no
    /// error. Note that usually, a successful `connect` call does not specify
    /// that there is a remote server listening on the port, rather, such an
    /// error would only be detected after the first send. If the OS returns an
    /// error for each of the specified addresses, the error returned from the
    /// last connection attempt (the last address) is returned.
    ///
    /// # Examples
    ///
    /// Creates a UDP socket bound to `127.0.0.1:3400` and connect the socket to
    /// `127.0.0.1:8080`:
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:3400").expect("couldn't bind to address");
    /// socket.connect("127.0.0.1:8080").expect("connect function failed");
    /// ```
    ///
    /// Unlike in the TCP case, passing an array of addresses to the `connect`
    /// function of a UDP socket is not a useful thing to do: The OS will be
    /// unable to determine whether something is listening on the remote
    /// address without the application sending data.
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn connect<A: ToSocketAddrs>(&self, addr: A) -> io::Result<()> {
        super::each_addr(addr, |addr| self.0.connect(addr))
    }

    /// Sends data on the socket to the remote address to which it is connected.
    ///
    /// The [`connect`] method will connect this socket to a remote address. This
    /// method will fail if the socket is not connected.
    ///
    /// [`connect`]: #method.connect
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.connect("127.0.0.1:8080").expect("connect function failed");
    /// socket.send(&[0, 1, 2]).expect("couldn't send message");
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn send(&self, buf: &[u8]) -> io::Result<usize> {
        self.0.send(buf)
    }

    /// Receives a single datagram message on the socket from the remote address to
    /// which it is connected. On success, returns the number of bytes read.
    ///
    /// The function must be called with valid byte array `buf` of sufficient size to
    /// hold the message bytes. If a message is too long to fit in the supplied buffer,
    /// excess bytes may be discarded.
    ///
    /// The [`connect`] method will connect this socket to a remote address. This
    /// method will fail if the socket is not connected.
    ///
    /// [`connect`]: #method.connect
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.connect("127.0.0.1:8080").expect("connect function failed");
    /// let mut buf = [0; 10];
    /// match socket.recv(&mut buf) {
    ///     Ok(received) => println!("received {} bytes {:?}", received, &buf[..received]),
    ///     Err(e) => println!("recv function failed: {:?}", e),
    /// }
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn recv(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.recv(buf)
    }

    /// Receives single datagram on the socket from the remote address to which it is
    /// connected, without removing the message from input queue. On success, returns
    /// the number of bytes peeked.
    ///
    /// The function must be called with valid byte array `buf` of sufficient size to
    /// hold the message bytes. If a message is too long to fit in the supplied buffer,
    /// excess bytes may be discarded.
    ///
    /// Successive calls return the same data. This is accomplished by passing
    /// `MSG_PEEK` as a flag to the underlying `recv` system call.
    ///
    /// Do not use this function to implement busy waiting, instead use `libc::poll` to
    /// synchronize IO events on one or more sockets.
    ///
    /// The [`connect`] method will connect this socket to a remote address. This
    /// method will fail if the socket is not connected.
    ///
    /// [`connect`]: #method.connect
    ///
    /// # Errors
    ///
    /// This method will fail if the socket is not connected. The `connect` method
    /// will connect this socket to a remote address.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:34254").expect("couldn't bind to address");
    /// socket.connect("127.0.0.1:8080").expect("connect function failed");
    /// let mut buf = [0; 10];
    /// match socket.peek(&mut buf) {
    ///     Ok(received) => println!("received {} bytes", received),
    ///     Err(e) => println!("peek function failed: {:?}", e),
    /// }
    /// ```
    #[stable(feature = "peek", since = "1.18.0")]
    pub fn peek(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.peek(buf)
    }

    /// Moves this UDP socket into or out of nonblocking mode.
    ///
    /// This will result in `recv`, `recv_from`, `send`, and `send_to`
    /// operations becoming nonblocking, i.e., immediately returning from their
    /// calls. If the IO operation is successful, `Ok` is returned and no
    /// further action is required. If the IO operation could not be completed
    /// and needs to be retried, an error with kind
    /// [`io::ErrorKind::WouldBlock`] is returned.
    ///
    /// On Unix platforms, calling this method corresponds to calling `fcntl`
    /// `FIONBIO`. On Windows calling this method corresponds to calling
    /// `ioctlsocket` `FIONBIO`.
    ///
    /// [`io::ErrorKind::WouldBlock`]: ../io/enum.ErrorKind.html#variant.WouldBlock
    ///
    /// # Examples
    ///
    /// Creates a UDP socket bound to `127.0.0.1:7878` and read bytes in
    /// nonblocking mode:
    ///
    /// ```no_run
    /// use std::io;
    /// use std::net::UdpSocket;
    ///
    /// let socket = UdpSocket::bind("127.0.0.1:7878").unwrap();
    /// socket.set_nonblocking(true).unwrap();
    ///
    /// # fn wait_for_fd() { unimplemented!() }
    /// let mut buf = [0; 10];
    /// let (num_bytes_read, _) = loop {
    ///     match socket.recv_from(&mut buf) {
    ///         Ok(n) => break n,
    ///         Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
    ///             // wait until network socket is ready, typically implemented
    ///             // via platform-specific APIs such as epoll or IOCP
    ///             wait_for_fd();
    ///         }
    ///         Err(e) => panic!("encountered IO error: {}", e),
    ///     }
    /// };
    /// println!("bytes: {:?}", &buf[..num_bytes_read]);
    /// ```
    #[stable(feature = "net2_mutators", since = "1.9.0")]
    pub fn set_nonblocking(&self, nonblocking: bool) -> io::Result<()> {
        self.0.set_nonblocking(nonblocking)
    }
}

impl AsInner<net_imp::UdpSocket> for UdpSocket {
    fn as_inner(&self) -> &net_imp::UdpSocket {
        &self.0
    }
}

impl FromInner<net_imp::UdpSocket> for UdpSocket {
    fn from_inner(inner: net_imp::UdpSocket) -> UdpSocket {
        UdpSocket(inner)
    }
}

impl IntoInner<net_imp::UdpSocket> for UdpSocket {
    fn into_inner(self) -> net_imp::UdpSocket {
        self.0
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl fmt::Debug for UdpSocket {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(all(test, not(any(target_os = "cloudabi", target_os = "emscripten", target_env = "sgx"))))]
mod tests {
    use crate::io::ErrorKind;
    use crate::net::test::{next_test_ip4, next_test_ip6};
    use crate::net::*;
    use crate::sync::mpsc::channel;
    use crate::sys_common::AsInner;
    use crate::thread;
    use crate::time::{Duration, Instant};

    fn each_ip(f: &mut dyn FnMut(SocketAddr, SocketAddr)) {
        f(next_test_ip4(), next_test_ip4());
        f(next_test_ip6(), next_test_ip6());
    }

    macro_rules! t {
        ($e:expr) => {
            match $e {
                Ok(t) => t,
                Err(e) => panic!("received error for `{}`: {}", stringify!($e), e),
            }
        };
    }

    #[test]
    fn bind_error() {
        match UdpSocket::bind("1.1.1.1:9999") {
            Ok(..) => panic!(),
            Err(e) => assert_eq!(e.kind(), ErrorKind::AddrNotAvailable),
        }
    }

    #[test]
    fn socket_smoke_test_ip4() {
        each_ip(&mut |server_ip, client_ip| {
            let (tx1, rx1) = channel();
            let (tx2, rx2) = channel();

            let _t = thread::spawn(move || {
                let client = t!(UdpSocket::bind(&client_ip));
                rx1.recv().unwrap();
                t!(client.send_to(&[99], &server_ip));
                tx2.send(()).unwrap();
            });

            let server = t!(UdpSocket::bind(&server_ip));
            tx1.send(()).unwrap();
            let mut buf = [0];
            let (nread, src) = t!(server.recv_from(&mut buf));
            assert_eq!(nread, 1);
            assert_eq!(buf[0], 99);
            assert_eq!(src, client_ip);
            rx2.recv().unwrap();
        })
    }

    #[test]
    fn socket_name() {
        each_ip(&mut |addr, _| {
            let server = t!(UdpSocket::bind(&addr));
            assert_eq!(addr, t!(server.local_addr()));
        })
    }

    #[test]
    fn socket_peer() {
        each_ip(&mut |addr1, addr2| {
            let server = t!(UdpSocket::bind(&addr1));
            assert_eq!(server.peer_addr().unwrap_err().kind(), ErrorKind::NotConnected);
            t!(server.connect(&addr2));
            assert_eq!(addr2, t!(server.peer_addr()));
        })
    }

    #[test]
    fn udp_clone_smoke() {
        each_ip(&mut |addr1, addr2| {
            let sock1 = t!(UdpSocket::bind(&addr1));
            let sock2 = t!(UdpSocket::bind(&addr2));

            let _t = thread::spawn(move || {
                let mut buf = [0, 0];
                assert_eq!(sock2.recv_from(&mut buf).unwrap(), (1, addr1));
                assert_eq!(buf[0], 1);
                t!(sock2.send_to(&[2], &addr1));
            });

            let sock3 = t!(sock1.try_clone());

            let (tx1, rx1) = channel();
            let (tx2, rx2) = channel();
            let _t = thread::spawn(move || {
                rx1.recv().unwrap();
                t!(sock3.send_to(&[1], &addr2));
                tx2.send(()).unwrap();
            });
            tx1.send(()).unwrap();
            let mut buf = [0, 0];
            assert_eq!(sock1.recv_from(&mut buf).unwrap(), (1, addr2));
            rx2.recv().unwrap();
        })
    }

    #[test]
    fn udp_clone_two_read() {
        each_ip(&mut |addr1, addr2| {
            let sock1 = t!(UdpSocket::bind(&addr1));
            let sock2 = t!(UdpSocket::bind(&addr2));
            let (tx1, rx) = channel();
            let tx2 = tx1.clone();

            let _t = thread::spawn(move || {
                t!(sock2.send_to(&[1], &addr1));
                rx.recv().unwrap();
                t!(sock2.send_to(&[2], &addr1));
                rx.recv().unwrap();
            });

            let sock3 = t!(sock1.try_clone());

            let (done, rx) = channel();
            let _t = thread::spawn(move || {
                let mut buf = [0, 0];
                t!(sock3.recv_from(&mut buf));
                tx2.send(()).unwrap();
                done.send(()).unwrap();
            });
            let mut buf = [0, 0];
            t!(sock1.recv_from(&mut buf));
            tx1.send(()).unwrap();

            rx.recv().unwrap();
        })
    }

    #[test]
    fn udp_clone_two_write() {
        each_ip(&mut |addr1, addr2| {
            let sock1 = t!(UdpSocket::bind(&addr1));
            let sock2 = t!(UdpSocket::bind(&addr2));

            let (tx, rx) = channel();
            let (serv_tx, serv_rx) = channel();

            let _t = thread::spawn(move || {
                let mut buf = [0, 1];
                rx.recv().unwrap();
                t!(sock2.recv_from(&mut buf));
                serv_tx.send(()).unwrap();
            });

            let sock3 = t!(sock1.try_clone());

            let (done, rx) = channel();
            let tx2 = tx.clone();
            let _t = thread::spawn(move || {
                match sock3.send_to(&[1], &addr2) {
                    Ok(..) => {
                        let _ = tx2.send(());
                    }
                    Err(..) => {}
                }
                done.send(()).unwrap();
            });
            match sock1.send_to(&[2], &addr2) {
                Ok(..) => {
                    let _ = tx.send(());
                }
                Err(..) => {}
            }
            drop(tx);

            rx.recv().unwrap();
            serv_rx.recv().unwrap();
        })
    }

    #[test]
    fn debug() {
        let name = if cfg!(windows) { "socket" } else { "fd" };
        let socket_addr = next_test_ip4();

        let udpsock = t!(UdpSocket::bind(&socket_addr));
        let udpsock_inner = udpsock.0.socket().as_inner();
        let compare =
            format!("UdpSocket {{ addr: {:?}, {}: {:?} }}", socket_addr, name, udpsock_inner);
        assert_eq!(format!("{:?}", udpsock), compare);
    }

    // FIXME: re-enabled openbsd/netbsd tests once their socket timeout code
    //        no longer has rounding errors.
    // VxWorks ignores SO_SNDTIMEO.
    #[cfg_attr(any(target_os = "netbsd", target_os = "openbsd", target_os = "vxworks"), ignore)]
    #[test]
    fn timeouts() {
        let addr = next_test_ip4();

        let stream = t!(UdpSocket::bind(&addr));
        let dur = Duration::new(15410, 0);

        assert_eq!(None, t!(stream.read_timeout()));

        t!(stream.set_read_timeout(Some(dur)));
        assert_eq!(Some(dur), t!(stream.read_timeout()));

        assert_eq!(None, t!(stream.write_timeout()));

        t!(stream.set_write_timeout(Some(dur)));
        assert_eq!(Some(dur), t!(stream.write_timeout()));

        t!(stream.set_read_timeout(None));
        assert_eq!(None, t!(stream.read_timeout()));

        t!(stream.set_write_timeout(None));
        assert_eq!(None, t!(stream.write_timeout()));
    }

    #[test]
    fn test_read_timeout() {
        let addr = next_test_ip4();

        let stream = t!(UdpSocket::bind(&addr));
        t!(stream.set_read_timeout(Some(Duration::from_millis(1000))));

        let mut buf = [0; 10];

        let start = Instant::now();
        loop {
            let kind = stream.recv_from(&mut buf).err().expect("expected error").kind();
            if kind != ErrorKind::Interrupted {
                assert!(
                    kind == ErrorKind::WouldBlock || kind == ErrorKind::TimedOut,
                    "unexpected_error: {:?}",
                    kind
                );
                break;
            }
        }
        assert!(start.elapsed() > Duration::from_millis(400));
    }

    #[test]
    fn test_read_with_timeout() {
        let addr = next_test_ip4();

        let stream = t!(UdpSocket::bind(&addr));
        t!(stream.set_read_timeout(Some(Duration::from_millis(1000))));

        t!(stream.send_to(b"hello world", &addr));

        let mut buf = [0; 11];
        t!(stream.recv_from(&mut buf));
        assert_eq!(b"hello world", &buf[..]);

        let start = Instant::now();
        loop {
            let kind = stream.recv_from(&mut buf).err().expect("expected error").kind();
            if kind != ErrorKind::Interrupted {
                assert!(
                    kind == ErrorKind::WouldBlock || kind == ErrorKind::TimedOut,
                    "unexpected_error: {:?}",
                    kind
                );
                break;
            }
        }
        assert!(start.elapsed() > Duration::from_millis(400));
    }

    // Ensure the `set_read_timeout` and `set_write_timeout` calls return errors
    // when passed zero Durations
    #[test]
    fn test_timeout_zero_duration() {
        let addr = next_test_ip4();

        let socket = t!(UdpSocket::bind(&addr));

        let result = socket.set_write_timeout(Some(Duration::new(0, 0)));
        let err = result.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidInput);

        let result = socket.set_read_timeout(Some(Duration::new(0, 0)));
        let err = result.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidInput);
    }

    #[test]
    fn connect_send_recv() {
        let addr = next_test_ip4();

        let socket = t!(UdpSocket::bind(&addr));
        t!(socket.connect(addr));

        t!(socket.send(b"hello world"));

        let mut buf = [0; 11];
        t!(socket.recv(&mut buf));
        assert_eq!(b"hello world", &buf[..]);
    }

    #[test]
    fn connect_send_peek_recv() {
        each_ip(&mut |addr, _| {
            let socket = t!(UdpSocket::bind(&addr));
            t!(socket.connect(addr));

            t!(socket.send(b"hello world"));

            for _ in 1..3 {
                let mut buf = [0; 11];
                let size = t!(socket.peek(&mut buf));
                assert_eq!(b"hello world", &buf[..]);
                assert_eq!(size, 11);
            }

            let mut buf = [0; 11];
            let size = t!(socket.recv(&mut buf));
            assert_eq!(b"hello world", &buf[..]);
            assert_eq!(size, 11);
        })
    }

    #[test]
    fn peek_from() {
        each_ip(&mut |addr, _| {
            let socket = t!(UdpSocket::bind(&addr));
            t!(socket.send_to(b"hello world", &addr));

            for _ in 1..3 {
                let mut buf = [0; 11];
                let (size, _) = t!(socket.peek_from(&mut buf));
                assert_eq!(b"hello world", &buf[..]);
                assert_eq!(size, 11);
            }

            let mut buf = [0; 11];
            let (size, _) = t!(socket.recv_from(&mut buf));
            assert_eq!(b"hello world", &buf[..]);
            assert_eq!(size, 11);
        })
    }

    #[test]
    fn ttl() {
        let ttl = 100;

        let addr = next_test_ip4();

        let stream = t!(UdpSocket::bind(&addr));

        t!(stream.set_ttl(ttl));
        assert_eq!(ttl, t!(stream.ttl()));
    }

    #[test]
    fn set_nonblocking() {
        each_ip(&mut |addr, _| {
            let socket = t!(UdpSocket::bind(&addr));

            t!(socket.set_nonblocking(true));
            t!(socket.set_nonblocking(false));

            t!(socket.connect(addr));

            t!(socket.set_nonblocking(false));
            t!(socket.set_nonblocking(true));

            let mut buf = [0];
            match socket.recv(&mut buf) {
                Ok(_) => panic!("expected error"),
                Err(ref e) if e.kind() == ErrorKind::WouldBlock => {}
                Err(e) => panic!("unexpected error {}", e),
            }
        })
    }
}
