# Temporal graph exploration

Submission [lax-623795](https://laxarchive.org/lax-623795/), proving upper and
lower bounds for temporal exploration in connected temporal graphs. The basic
definitions of temporal graphs, timed vertex visits, strict temporal walks,
walk concatenation, and time-bounded reachability are included locally.

A temporal graph is represented by a positive finite lifetime and a simple
graph at each consecutive time step. Temporal walks record the vertex occupied
at each visited time, permit waiting at a vertex, and require traversal times to
increase strictly. Compatible walks can be concatenated when they meet at the
same vertex and time.

The upper-bound argument studies the set of vertices reachable from a nonempty
starting set during a fixed interval. As long as this reachable set is not the
whole vertex set, connectedness of the next snapshot supplies a boundary edge.
Traversing that edge at the additional time step reaches a new vertex and
strictly enlarges the reachable set.

The lower-bound development complements this growth argument by formalizing
connected temporal graphs whose exploration cannot finish sooner. Together,
the upper and lower bounds characterize the worst-case exploration behavior of
connected temporal graphs.

Concept statements and definitions live in `concepts/`; kernel-checked proofs
live separately in `proofs/`, following the Lax concept/proof split. Run
`lax build . --replay` from this directory to validate the package and replay
its proofs.

The submission targets Lean and Mathlib 4.33.0 and is based on Thomas Erlebach,
Michael Hoffmann, and Frank Kammer, *On temporal graph exploration*, Journal of
Computer and System Sciences 119 (2021), 1–18.
