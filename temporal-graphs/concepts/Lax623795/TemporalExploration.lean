import Lax623795.TemporalGraphs

/-!
---
title: Growth of Temporal Reachability
type: theorem
---

Let `X` be a nonempty proper set of vertices in an always-connected temporal
graph. Fix a nonempty time interval ending at `endTime`. If the vertices reachable
from `X` during this interval do not yet comprise the whole vertex set, extending
the interval by one valid time step strictly enlarges the reachable vertex set.
-/

universe u

namespace Lax623795.TemporalExploration

open Lax623795.TemporalGraphs

/-- Extending a reachability interval by one connected snapshot discovers a new vertex. -/
axiom reachableVertexSet_ssubset_next
    {V : Type u} (G : TemporalGraph V) (X : Set V)
    (startTime endTime nextTime : G.Timestep)
    (h_connected : G.AlwaysConnected)
    (hX_nonempty : X.Nonempty)
    (_hX_proper : X ≠ Set.univ)
    (h_interval : startTime.val.val ≤ endTime.val.val)
    (h_next : nextTime.val.val = endTime.val.val + 1)
    (h_reachable_proper :
      G.reachableVertexSet X startTime endTime ≠ Set.univ) :
    G.reachableVertexSet X startTime endTime ⊂
      G.reachableVertexSet X startTime nextTime

end Lax623795.TemporalExploration
