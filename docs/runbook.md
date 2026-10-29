# Running the NNTP server

The server is one process per spool: the session's program, compiled by CakeML, with its host `native/nntp_host.c`. This page is how to install, run, watch, back up and restore it; the nntp lane's `operations` check runs it on a disposable instance.

## Build and install

```sh
lake build dn-compiler
python3 scripts/build_server.py --cake "$(python3 scripts/bootstrap_tool.py cake)" --out build/server
install -m 0755 build/server/dragons-nntpd /usr/local/bin/
install -d -m 0700 -o news -g news /var/spool/dragons-net /run/dragons-net
```

The executable needs only the C library. The spool and the run directory belong to the user the server runs as, with no other access; the run directory should be on a file system the boot clears, such as `/run`.

## Settings

Settings come as options or from a file given by `--config FILE`: a setting a line, its name, white space and its value; a line starting with `#` is a comment. A setting unknown, without a value, or given twice where it is taken once, a file's and an option alike, refuses the start with status 2, naming the line.

`--check-config FILE` checks the settings and that the store's directories open, writes them as JSON and starts nothing; it takes no lock and binds no port.

| Setting | What it gives | Default |
| --- | --- | --- |
| `address`, `port` | Where to listen | 127.0.0.1, a port the kernel picks |
| `revision`, `source` | The revision the replies name, at most 64 octets, and where its source is offered (AGPL), at most 200; required | — |
| `spool`, `run-dir` | The store's directory and where a failed sync's mark is copied | No store: nobody may post |
| `path-identity` | The server's name in Path and Xref, at most 200 octets | none |
| `group` | A group carried, once a group, at most 64 of at most 64 octets | none |
| `post-from` | A network that may post, as an address and a prefix length, at most 16 | 127.0.0.0/8 and ::1/128 |
| `send-buffer` | SO_SNDBUF of each connection, in octets | the kernel's |

```
revision v1
source https://example.org/dragons-net
spool /var/spool/dragons-net
run-dir /run/dragons-net
path-identity news.example.org
group local.general
post-from 192.168.1.0/24
```

Run without systemd, the file gives `address` and `port` too, such as `address ::` and `port 1119`. The limits are the specification's and need no setting: 64 connections, a first command within 10 s, 30 min of inactivity, 3 min for a line, 30 min for an article. Each bound and what holds it is in [architecture](architecture.md#bounds).

## Privileges

The server needs no privilege. For port 119 systemd can hand it the listening socket: started with LISTEN_PID naming it and LISTEN_FDS 1, it listens on descriptor 3, an IPv4 or IPv6 stream socket, and `address` and `port` are refused, so the file leaves them out. Connections wait in the kernel until recovery ends.

The units below are the shape; the lane tests the socket's hand-over, not systemd itself. `RuntimeDirectory` keeps the run directory under `/run`, kept across stops so that a failed sync's mark stays.

```ini
# dragons-nntpd.socket
[Socket]
ListenStream=119

[Install]
WantedBy=sockets.target

# dragons-nntpd.service
[Service]
User=news
ExecStart=/usr/local/bin/dragons-nntpd --config /etc/dragons-nntpd.conf
RuntimeDirectory=dragons-net
RuntimeDirectoryPreserve=yes
NoNewPrivileges=yes
ProtectSystem=strict
ReadWritePaths=/var/spool/dragons-net
```

## Stopping and how it ends

SIGTERM or SIGINT closes every socket, drops the file jobs not begun, waits up to 30 s for those running, and ends with status 0.

Other statuses: 1, the program broke the host's contract; 2, a setting or a system call failed; 3, the host broke the program's, the code named; 4, the store was refused at start, the reason named.

## Counters

SIGUSR1 writes one line of counters to stderr, and a stop on a signal writes it again. It counts the connections taken and how those ended: gracefully, at once, or by the client or the network.

It counts the octets read and sent, and the pauses in accepting when descriptors or memory ran out. Last, the file jobs, and those that failed for want of space, on an I/O error or otherwise.

The line holds no address, name or octet a client sent; the log of connections, which names each poster's address, is apart.

## Backup and restore

Stop the server, copy the spool, start it again. To restore, put the copy in place of the spool, or name the copy's directory as `spool`, and start: the start reads the journal and serves every article it holds.

## Recovery

Every start recovers the store before it listens. A journal torn in its last record, as a crash leaves it, is cut back to the records before, and the articles those name are served. A store corrupt otherwise refuses the start with status 4.

After a sync failed, its mark refuses every start until the machine restarts, since data the kernel could not write may still be lost.

## What is supported

One process on one spool, held by a lock, on Linux, on a local file system whose syncs are kept. Not supported: more than one server on a spool, a network file system, an exchange between servers.

What the lanes establish is in the [baseline](baseline.md): the server killed at each file operation ([crashes](baseline.md#crashes)), power lost at each, on LazyFS ([power loss](baseline.md#power-loss)), each operation failing ([faults](baseline.md#faults)).
