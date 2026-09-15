import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Chain
import Mathlib.Data.PNat.Notation

/-!
---
title: Temporal Graphs
type: definition
---

A temporal graph has a positive finite lifetime and an undirected, loop-free graph
at each consecutive positive time step. Its footprint contains every edge that
appears during its lifetime, and it is always connected when every snapshot is
connected. A temporal walk may be empty, with no visited vertices, or nonempty,
with a start time, an end time, and snapshot edges traversed at strictly increasing
times. A nonempty walk may remain at one vertex throughout its time interval. The
reachable vertex set of `X` in a time interval consists of the vertices reachable
within that interval from at least one vertex of `X`.
-/

universe u

namespace Lax623795.TemporalGraphs

/--
A finite-lifetime temporal graph on the vertex type `V`.

The positive natural number `lifetime` is the final time step. The snapshots are
indexed consecutively by the positive times `1, ..., lifetime`.
Each snapshot is the undirected, loop-free simple graph whose edges are
active at that time. The vertex type `V` is not required to be finite.
-/
structure TemporalGraph (V : Type u) where
  lifetime : ℕ+
  snapshot : { t : ℕ+ // t.val ≤ lifetime.val } → SimpleGraph V

namespace TemporalGraph

/-- A valid positive time step during the lifetime of `G`. -/
abbrev Timestep {V : Type u} (G : TemporalGraph V) :=
  { t : ℕ+ // t.val ≤ G.lifetime.val }

/-- Two vertices are adjacent in `G` at time `t`. -/
def AdjAt {V : Type u} (G : TemporalGraph V)
    (t : G.Timestep) (x y : V) : Prop :=
  (G.snapshot t).Adj x y

/-- The set of vertices adjacent to `v` in `G` at time `t`. -/
def neighborSetAt {V : Type u} (G : TemporalGraph V)
    (t : G.Timestep) (v : V) : Set V :=
  (G.snapshot t).neighborSet v

/-- The static graph containing every edge that appears in any snapshot of `G`. -/
def footprint {V : Type u} (G : TemporalGraph V) : SimpleGraph V :=
  ⨆ t, G.snapshot t

/-- A temporal graph is always connected when each of its snapshots is connected. -/
def AlwaysConnected {V : Type u} (G : TemporalGraph V) : Prop :=
  ∀ t, (G.snapshot t).Connected

/-- A visit records the vertex occupied by a walk at a particular time step. -/
structure Visit {V : Type u} (G : TemporalGraph V) where
  vertex : V
  timestep : G.Timestep

/-- `next` may follow `current` when time increases and the walk waits or traverses an edge. -/
def IsValidSuccessor {V : Type u} (G : TemporalGraph V)
    (current next : G.Visit) : Prop :=
  current.timestep.val.val < next.timestep.val.val ∧
    (current.vertex = next.vertex ∨
      G.AdjAt next.timestep current.vertex next.vertex)

/--
A temporal walk is a chain of timed vertex visits.

Times strictly increase. Between consecutive visits the walk either remains at the
same vertex or traverses an edge active at the later time. The empty list is the
temporal walk with no visited vertices.
-/
structure TemporalWalk {V : Type u} (G : TemporalGraph V) where
  visits : List G.Visit
  chain : visits.IsChain (G.IsValidSuccessor)

namespace TemporalWalk

/-- The temporal walk with no visited vertices. -/
def empty {V : Type u} (G : TemporalGraph V) : G.TemporalWalk where
  visits := []
  chain := .nil

/-- The instantaneous temporal walk consisting of one visit. -/
def singleton {V : Type u} (G : TemporalGraph V)
    (v : V) (t : G.Timestep) : G.TemporalWalk where
  visits := [⟨v, t⟩]
  chain := .singleton _

/-- A temporal walk that stays at `v` from `startTime` until the later `endTime`. -/
def stay {V : Type u} (G : TemporalGraph V) (v : V)
    (startTime endTime : G.Timestep)
    (h : startTime.val.val < endTime.val.val) : G.TemporalWalk where
  visits := [⟨v, startTime⟩, ⟨v, endTime⟩]
  chain := by
    simp [IsValidSuccessor, h]

/-- The first visit of `W`, or `none` when `W` is empty. -/
def startVisit? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option G.Visit :=
  W.visits.head?

/-- The final visit of `W`, or `none` when `W` is empty. -/
def endVisit? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option G.Visit :=
  W.visits.getLast?

/-- The starting vertex of `W`, or `none` when `W` is empty. -/
def startVertex? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option V :=
  W.startVisit?.map Visit.vertex

/-- The final vertex of `W`, or `none` when `W` is empty. -/
def endVertex? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option V :=
  W.endVisit?.map Visit.vertex

/-- The starting time of `W`, or `none` when `W` is empty. -/
def startTime? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option G.Timestep :=
  W.startVisit?.map Visit.timestep

/-- The final time of `W`, or `none` when `W` is empty. -/
def endTime? {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk) : Option G.Timestep :=
  W.endVisit?.map Visit.timestep

/-- Every visit of `W` occurs in the inclusive interval from `startTime` to `endTime`. -/
def IsWithin {V : Type u} {G : TemporalGraph V} (W : G.TemporalWalk)
    (startTime endTime : G.Timestep) : Prop :=
  ∀ visit ∈ W.visits,
    startTime.val.val ≤ visit.timestep.val.val ∧
      visit.timestep.val.val ≤ endTime.val.val

/--
Two temporal walks can be concatenated when either one is empty, or when the first
ends at exactly the timed vertex where the second begins.
-/
def CanConcat {V : Type u} {G : TemporalGraph V}
    (W W' : G.TemporalWalk) : Prop :=
  match W.visits, W'.visits with
  | [], _ => True
  | _, [] => True
  | left, first :: _ => left.getLast? = some first

/--
Concatenate compatible temporal walks, counting their common timed vertex only once.
The empty temporal walk is a left and right identity.
-/
def concat {V : Type u} {G : TemporalGraph V}
    (W W' : G.TemporalWalk) (h : W.CanConcat W') : G.TemporalWalk := by
  rcases W with ⟨visits, chain⟩
  rcases W' with ⟨visits', chain'⟩
  cases visits with
  | nil => exact ⟨visits', chain'⟩
  | cons first rest =>
      cases visits' with
      | nil => exact ⟨first :: rest, chain⟩
      | cons first' rest' =>
          refine ⟨(first :: rest) ++ rest', ?_⟩
          cases rest' with
          | nil => simpa using chain
          | cons second' tail' =>
              apply chain.append chain'.tail
              intro last hlast next hnext
              have hjoin : (first :: rest).getLast? = some first' := h
              have hlast_eq : last = first' := by
                rw [hjoin] at hlast
                have hlast_eq' : first' = last := by simpa using hlast
                exact hlast_eq'.symm
              have hnext_eq : next = second' := by
                have hnext_eq' : second' = next := by simpa using hnext
                exact hnext_eq'.symm
              simpa [hlast_eq, hnext_eq] using chain'.rel

end TemporalWalk

/-- Vertex `finish` is temporally reachable from `start` if a temporal walk joins them. -/
def Reachable {V : Type u} (G : TemporalGraph V) (start finish : V) : Prop :=
  ∃ W : G.TemporalWalk,
    W.startVertex? = some start ∧ W.endVertex? = some finish

/--
The vertices reachable within `[startTime, endTime]` from at least one vertex in `X`.
-/
def reachableVertexSet {V : Type u} (G : TemporalGraph V) (X : Set V)
    (startTime endTime : G.Timestep) : Set V :=
  { finish | ∃ start ∈ X, ∃ W : G.TemporalWalk,
      W.startVertex? = some start ∧
      W.endVertex? = some finish ∧
      W.IsWithin startTime endTime }

end TemporalGraph

end Lax623795.TemporalGraphs
