EWD998
================
Markus A Kuppe
(2021-08-30)

The [specification](./EWD998.tla) in this directory models termination
detection in a ring as given by Shmuel Safra in
[EWD 998](https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF). EWD
998 is an extension of a simpler algorithm described in [EWD
840](../ewd840). Compared to EWD 840, this algorithm supports
asynchronous message delivery. However, it still assumes reliable
message channels and non-faulty nodes. For TLA+ learners, it is best to
study EWD840 first and then read the TLA+ spec of
[EWD998.tla](./EWD998.tla).

For readers familiar with TLA+:

EWD998.tla refines the abstraction
[AsyncTerminationDetection](./AsyncTerminationDetection.tla) under the
refinement mapping given in EWD998.tla. This mapping has been
model-checked with TLC. Additionally, the spec
[AsyncTerminationDetection\_proof](./AsyncTerminationDetection_proof.tla)
proves the main safety properties for module AsyncTerminationDetection,
and refinement of
[SyncTerminationDetection.tla](../ewd840/SyncTerminationDetection.tla).
Elsewhere, SyncTerminationDetection is refined by
[EWD840.tla](../ewd840/EWD840.tla).

    SyncTerminationDetection < EWD840
                             < AsyncTerminationDetection 
                                  < EWD998
                                      < EWD998Chan
                                          < EWD998ChanID

The spec [EWD998Chan.tla](./EWD998Chan.tla) refines EWD998.tla by adding
inboxes. [EWD998ChanID.tla](./EWD998ChanID.tla) refines EWD998Chan.tla
and replace natural numbers as node identifiers with hostnames
(arbitrary strings actually). EWD998ChanID.tla also shows how to model
[vector clocks](https://en.wikipedia.org/wiki/Vector_clock) in TLA+,
which [EWD998ChanID\_shiviz.tla](./EWD998ChanID_shiviz.tla) exploits to
visualize traces with [Shiviz](https://bestchai.bitbucket.io/shiviz/).
The spec [EWD998ChanID\_export.tla](./EWD998ChanID_export.tla)
demonstrates how to export TLC traces to Json. Below is an animation of
the termination detection process for six nodes. It was created with
[EWD998\_anim.tla](./EWD998_anim.tla).

![Termination detection with EWD998 with six processes](./EWD998.gif)
