import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.PNat.Notation

universe u

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

/-- Two vertices are adjacent in `G` at time `t`. -/
def AdjAt {V : Type u} (G : TemporalGraph V)
    (t : { t : ℕ+ // t.val ≤ G.lifetime.val }) (x y : V) : Prop :=
  (G.snapshot t).Adj x y

/-- The static graph containing every edge that appears in any snapshot of `G`. -/
def footprint {V : Type u} (G : TemporalGraph V) : SimpleGraph V :=
  ⨆ t, G.snapshot t

/-- A temporal graph is always connected when each of its snapshots is connected. -/
def AlwaysConnected {V : Type u} (G : TemporalGraph V) : Prop :=
  ∀ t, (G.snapshot t).Connected

end TemporalGraph
