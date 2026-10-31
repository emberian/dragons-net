# Measurements

How fast the hosts are, measured against one another under one load. The numbers below were taken on one machine and are relative: no check judges them, and a shared CI runner would not hold them still. Correctness is the lanes' business; here a wrong reply or a lost connection stops the measurement.

## The load

`native/load.c` is an open-loop load: requests fall due at a fixed rate on a schedule that does not wait for the server, one in flight a connection. A request late to go keeps the time it fell due. Its latency runs from then to its reply's last octet, as wrk2 measures, so a stall shows in every request it delayed.

* Each reply is compared octet by octet with the one it must be, read from the same server before the run; octets with no request in flight are wrong too.
* The load counts over a window after a warm-up, and says on stderr when it opens and closes. A reply is timed when its request fell due in the window, and counted as served when it arrived in it.
* A request of the window still unanswered two seconds after it is owed, and timed to that moment, a lower bound. No request falls due after the window.
* Its threads sleep with a timer slack of 1 ns, and how late each request went is kept apart from its latency. Its own CPU time is taken over the window too.
* Latencies go into a log-linear histogram: exact below 128 ns, then 64 cells a power of two, under 1.6% wide.
* Two slow readers a run, each asking a 4 KiB receive buffer, which Linux doubles, ask for 16 MiB of replies at once and take 16 octets every 10 ms. The server holds output it cannot send while it serves the rest; once the window closes they read the rest at once.

`native/alloc_count.c`, loaded with LD_PRELOAD, counts the server's heap allocations into a file read at any moment. `native/nodelay.c` sets TCP_NODELAY on each connection a server accepts.

## Running it

On Linux x86-64, after `bash scripts/check.sh build`, in the sandbox or a quiet machine:

```sh
cake=$(python3 scripts/bootstrap_tool.py cake)
python3 scripts/bench.py measure --cake "$cake" --server-cpus 2,3,4,5
```

It writes `build/bench/measured.json`, and `python3 scripts/bench.py table` prints the tables below from it. The load's four threads take CPUs of cores the server's CPUs do not share, since two hardware threads of a core share its units.

All the hosts are started at once, each on its cores. For each the rate doubles from 2,000 a second, or halves, until the host keeps it and loses twice it; then it goes up from the highest kept by a quarter at a time.

A rate is kept when replies come within 3% of it, none is owed and the 99th percentile is under 20 ms. It is marked load-bound when the load's threads were busy over 70% of the window: the load, not the host, may be what saturated.

The highest rate kept is run again for as long as a round's run, or the next one down if it is lost, and each NNTP command is run alone at 1,000 a second.

Then five rounds, each starting every host anew and taking them in another order. Steady load runs at half the lowest rate any host of its kind keeps, the same for all, so that their costs compare. Overload runs at one and a half times the host's own; each run warms up 10 s and counts 10 s.

The server's CPU time, from the kernel's count of the time each of its threads and processes ran, context switches and allocations are taken over the window and shared by the replies served in it. Allocations come from a run with the counter.

System calls come from a run at 2,000 a second under `strace -c`, too slow to time. It has no slow readers: strace counts on after the window, while they take their 16 MiB.

`python3 scripts/bench.py profile --cake "$cake" --command ARTICLE` runs the NNTP server under callgrind, waiting with poll, with one command of the mix at 200 a second for five seconds, or the whole mix without `--command`. It counts each function's instructions, less those of a run that only starts the server.

`python3 scripts/bench.py check` is the `bench` lane. It holds the load to nine servers of its own, seven faulty: a wrong octet, a slow reader's, an octet too many, a closed connection, a silent one, late answers, a stall; and two right, one forking. Then a second of load with slow readers on each host, every reply right and none owed.

## The hosts

| Host | What it is | Connections |
|---|---|---|
| `echo-poll` | `native/echo_server.c`, the reference, one thread | 30 and 2 slow readers, of 32 slots |
| `echo-uring-1` | `native/echo_uring.c`, one thread | the same |
| `echo-uring-4` | the same, a thread a core on four cores | the same |
| `nntp-poll` | the NNTP server, `--io poll`: one thread serving, two for file jobs, on one core | 60 and 2 slow readers, of 64 |
| `nntp-uring` | the NNTP server on io_uring, its default, on one core alike | the same |
| `inn` | INN's reader, `nnrpd -D`, a process a connection, on one core | the same |
| `inn-nodelay` | the same, with TCP_NODELAY set by `native/nodelay.c` | the same |

Echo payloads are 64, 512 and 4,096 octets, six, three and one of every ten. NNTP connections select a group of 200 articles, then send a reader's mix over five articles: ARTICLE of each, two of them by Message-ID too, HEAD of two, STAT, OVER of twenty articles and GROUP.

INN, Ubuntu's 2.7.2~20240212, serves the same 200 articles, read off our server: its spool is written as files, and `makehistory` builds its history and overview. `nnrpd` reads them without `innd`, which runs only as the user news. It is used where it is installed, as in the sandbox.

`nnrpd` writes a reply with a body in two calls without TCP_NODELAY, and the second waits for a delayed acknowledgement, 40 ms, once the first is unacknowledged. Sixty connections, ten replies of the mix's twelve with a body, come to some 1,800 a second. `inn` shows INN as it runs, `inn-nodelay` what its code can do.

## Results

[bench-results.json](bench-results.json) records the machine, the C compiler and its flags, and every run: the rounds whole, with the load's counts and the latencies' cells; the sweeps and the commands as summaries.

On an AMD Ryzen 7 8745HS with 16 CPUs, two a core, Linux 7.0, the `powersave` governor and boost on. A host of one thread runs on CPU 2, `echo-uring-4` on CPUs 2 to 5; the load runs on CPUs 1, 6, 7 and 9, of other cores.

Steady load is 96,000 a second for the echo hosts and 750 for the NNTP ones. Figures are medians of five rounds, with the least and greatest, a range that holds the median of such runs fifteen times in sixteen.

Kept rates come from one sweep, confirmed by a run as long as a round's; the rest from one run each.

| Host | Kept, replies/s | CPU µs a reply there | Steady p50, µs | Steady p99, µs | Sent late p99, µs | CPU µs a reply | In the kernel | Switches a reply | Allocations a reply | VmHWM, MiB | Overload, replies/s | Calls a reply at 2,000/s |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `echo-poll` | 192,000 | 5.2 | 28 (28 to 29) | 44 (42 to 46) | 14 | 8.4 (8.4 to 8.6) | 83% | 0.13 | 0.00 | 1.9 | 214,132 | 3.8 |
| `echo-uring-1` | 224,000 | 4.5 | 16 (16 to 16) | 29 (28 to 31) | 13 | 5.9 (5.9 to 6.0) | 87% | 0.27 | 0.00 | 2.2 | 251,163 | 1.9 |
| `echo-uring-4` | 256,000 (load-bound) | 7.1 | 17 (16 to 17) | 33 (32 to 35) | 13 | 8.3 (7.9 to 8.6) | 84% | 0.84 | 0.00 | 3.2 | 384,000 | 1.9 |
| `nntp-poll` | 3,500 | 257.4 | 582 (582 to 598) | 5,571 (5,439 to 5,636) | 137 | 577.2 (573.8 to 578.8) | 41% | 17.74 | 0.00 | 4.2 | 4,041 | 37.4 |
| `nntp-uring` | 4,000 | 233.8 | 532 (524 to 541) | 5,308 (5,308 to 5,439) | 137 | 534.9 (533.1 to 538.5) | 34% | 18.39 | 0.00 | 4.2 | 4,168 | 34.8 |
| `inn` | 1,500 | 72.1 | 225 (197 to 246) | 1,327 (1,180 to 1,343) | 827 | 127.2 (105.5 to 132.4) | 74% | n/a | 15.40 | n/a | 1,791 | 13.1 |
| `inn-nodelay` | 28,000 | 33.5 | 197 (180 to 203) | 1,180 (1,114 to 1,196) | 713 | 103.2 (100.7 to 111.2) | 84% | n/a | 15.21 | n/a | 30,144 | 13.1 |

| Command alone, 1,000/s | Octets | `nntp-poll` CPU µs, p50 µs | `nntp-uring` CPU µs, p50 µs | `inn` CPU µs, p50 µs | `inn-nodelay` CPU µs, p50 µs |
|---|---|---|---|---|---|
| ARTICLE | 4,201 | 354, 463 | 298, 406 | 69, 94 | 73, 94 |
| ARTICLE <id> | 4,199 | 349, 459 | 301, 406 | 79, 104 | 78, 90 |
| HEAD | 378 | 194, 260 | 169, 217 | 68, 87 | 72, 95 |
| STAT | 25 | 57, 63 | 33, 88 | 64, 90 | 65, 91 |
| OVER | 2,672 | 1,446, not kept | 1,424, not kept | 119, 147 | 117, 145 |
| GROUP | 26 | 58, 75 | 35, 51 | 42, 62 | 41, 60 |

* The echo on io_uring keeps a sixth more than on poll, with three tenths less CPU a reply and lower latency; at 2,000 a second it makes half the system calls.
* Four threads keep 256,000 a second, the load's limit: past it the load's threads were busy all the window, and overloaded at 384,000 the host served every request.
* The NNTP server keeps 3,500 a second on one core waiting with poll, 4,000 with io_uring, which costs it 7% less CPU at 750 a second. It allocates nothing while it serves.
* INN as it runs keeps 1,500 a second: each reply with a body waits for a delayed acknowledgement. With TCP_NODELAY it keeps 28,000, seven times our server, with a fifth of its CPU a reply.
* CPU a reply falls as the rate rises: at the kept rate it is a third to three fifths of its figure at 750 a second, ours and INN's alike. The steady columns compare hosts at one rate. Another session gave steady CPU within 3% of these, INN with TCP_NODELAY within 12%.
* Alone at 1,000 a second, STAT and GROUP cost our server on io_uring less than they cost INN; HEAD over twice as much, ARTICLE four times, and OVER, not kept, twelve times.
* The load sent requests late by some 13 µs at the 99th percentile to the echo hosts, 137 µs to ours and 710 to 830 µs to INN's; their latencies count it.
* The slow readers held the echo's output: io_uring's sends to them were taken in part 20 times on one thread and 22 on four, poll's never.
* Overloaded, each host but `echo-uring-4` serves about what it keeps. Latencies then grow with the run's length, as owed requests are timed to its end, so they are not shown.

## Bottlenecks

From the commands alone above, and from `bench.py profile`: the instructions of five seconds at 200 a second by function, less those of the server's start. The mix served 581 replies, OVER slowed by callgrind; ARTICLE alone 996, STAT 999. Callgrind knows CakeML's functions by their labels only, so a share can belong to code that follows a label.

* **Mostly the session's program.** A third to two fifths of the NNTP server's time is in the kernel, on the host's calls below. Of the instructions in user space, the host's functions and the copies they make take some 5% on the mix, 6% on ARTICLE and 9% on STAT; the program takes the rest.
* **Octets given one at a time.** ARTICLE of 4,201 octets costs some 130 µs more than HEAD of two of its articles, 34 ns an octet: `readPiece` copies them one at a time. Callgrind charges two fifths of ARTICLE's instructions to `readDone`, over a third to `readOutSize`, which has no loop: most may be `readPiece`'s copy, after its label.
* **Checking each file.** A file is checked for its CRC-32C and scanned for its lines an octet at a time as it is read (`readDone`): HEAD reads its whole file, and costs some 135 µs more than STAT.
* **OVER reads every article it lists.** Each OVER opens, checks and scans the header of every article in its range, matching field names an octet at a time with a call each (`nameByte`, 58% of the mix's instructions). It costs some 1,420 µs a reply and is not kept at 1,000 a second; INN reads its overview database in 117.
* **Finding an article, and the turn.** STAT reads no file and costs 33 to 57 µs. Finding an article by its number scans its group (`groupScan`): half of STAT's instructions with 200 articles. The turn's visits of every connection slot (`connAct`, `connSettle`) take a sixth.
* **File jobs through threads, replies in pieces.** A reply takes 35 to 37 system calls at 2,000 a second. Its file's open, read and close go to a thread and back through some 18 futex, read and write calls. Each job's data is copied whole into the queue and out, the profile's `memcpy`. A reply leaves in 512-octet actions.

On the echo the host is nearly all there is: four fifths of its time is in the kernel.

## What to try

In order of the CPU each would save, estimated from the commands alone at 1,000 a second on io_uring, where a reply of the mix costs some 330 µs on average:

1. An overview database: each article's overview line kept by POST in the store, so that OVER reads no article. At INN's cost, it saves some 110 µs a mix reply.
2. A file checked once: its CRC-32C a word a step, or kept as checked while the server runs. Of the 135 µs HEAD costs over STAT on nine replies of twelve, up to some 100 µs.
3. Octets given in blocks: a copy of the reply's run of the file at once, in actions larger than 512 octets. Of ARTICLE's 130 µs over HEAD on seven replies of twelve, some 75 µs.
4. An article found by its number directly, and a turn that visits only the connections with something to do: up to two thirds of STAT's 33 µs, on every reply.
5. File operations on the ring itself (IORING_OP_OPENAT, READ, CLOSE) instead of threads, read into the session's buffer: no futex, no wake-up and no copy through the queue. Not estimated: its share is in the kernel's.
6. On the echo: multishot receives and provided buffers, which the liburing authors name as io_uring's gain for networking.
