import Lax623795.TemporalExploration

universe u

namespace Lax623795Proofs

open Lax623795.TemporalGraphs

/--
---
conclusion: Lax623795.TemporalExploration.reachableVertexSet_ssubset_next
---
-/
theorem reachableVertexSet_ssubset_next
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
      G.reachableVertexSet X startTime nextTime := by
  let R := G.reachableVertexSet X startTime endTime
  let Rnext := G.reachableVertexSet X startTime nextTime
  change R ⊂ Rnext
  change R ≠ Set.univ at h_reachable_proper
  apply Set.ssubset_iff_exists.mpr
  constructor
  · intro finish hfinish
    rcases hfinish with ⟨start, hstart, W, hWstart, hWfinish, hWwithin⟩
    refine ⟨start, hstart, W, hWstart, hWfinish, ?_⟩
    intro visit hvisit
    obtain ⟨hlower, hupper⟩ := hWwithin visit hvisit
    exact ⟨hlower, by omega⟩
  · obtain ⟨initial, hinitial⟩ := hX_nonempty
    have hinitial_R : initial ∈ R := by
      refine ⟨initial, hinitial, TemporalGraph.TemporalWalk.singleton G initial startTime,
        ?_, ?_, ?_⟩
      · rfl
      · rfl
      · intro visit hvisit
        simp only [TemporalGraph.TemporalWalk.singleton, List.mem_singleton] at hvisit
        subst visit
        exact ⟨le_rfl, h_interval⟩
    obtain ⟨outside, houtside⟩ :=
      (Set.ne_univ_iff_exists_notMem R).mp h_reachable_proper
    obtain ⟨staticWalk⟩ := (h_connected nextTime) initial outside
    obtain ⟨dart, _hdart, hdart_start, hdart_end⟩ :=
      staticWalk.exists_boundary_dart R hinitial_R houtside
    rcases hdart_start with ⟨start, hstart, W, hWstart, hWend, hWwithin⟩
    have hW_nonempty : W.visits ≠ [] := by
      intro hnil
      simp [TemporalGraph.TemporalWalk.endVertex?,
        TemporalGraph.TemporalWalk.endVisit?, hnil] at hWend
    let lastVisit := W.visits.getLast hW_nonempty
    have hlast_mem : lastVisit ∈ W.visits := by
      exact List.getLast_mem hW_nonempty
    have hlast_vertex : lastVisit.vertex = dart.fst := by
      simpa [TemporalGraph.TemporalWalk.endVertex?,
        TemporalGraph.TemporalWalk.endVisit?,
        List.getLast?_eq_some_getLast hW_nonempty, lastVisit] using hWend
    have hlast_within := hWwithin lastVisit hlast_mem
    have hlast_time_lt : lastVisit.timestep.val.val < nextTime.val.val := by
      omega
    let nextVisit : G.Visit := ⟨dart.snd, nextTime⟩
    have hadjacent : G.AdjAt nextTime lastVisit.vertex dart.snd := by
      change (G.snapshot nextTime).Adj lastVisit.vertex dart.snd
      rw [hlast_vertex]
      exact dart.adj
    have hsuccessor : G.IsValidSuccessor lastVisit nextVisit := by
      refine ⟨hlast_time_lt, Or.inr ?_⟩
      simpa [nextVisit] using hadjacent
    let Wnext : G.TemporalWalk :=
      { visits := W.visits ++ [nextVisit]
        chain := W.chain.append (.singleton _) (by
          intro last hlast next hnext
          have hgetLast : W.visits.getLast? = some lastVisit := by
            exact List.getLast?_eq_some_getLast hW_nonempty
          have hlast_eq : last = lastVisit := by
            rw [hgetLast] at hlast
            have hlast_eq' : lastVisit = last := by simpa using hlast
            exact hlast_eq'.symm
          have hnext_eq : next = nextVisit := by
            have hnext_eq' : nextVisit = next := by simpa using hnext
            exact hnext_eq'.symm
          simpa [hlast_eq, hnext_eq] using hsuccessor) }
    have hWnext_start : Wnext.startVertex? = some start := by
      change ((W.visits ++ [nextVisit]).head?).map
        TemporalGraph.Visit.vertex = some start
      rw [List.head?_append_of_ne_nil _ hW_nonempty]
      exact hWstart
    have hWnext_end : Wnext.endVertex? = some dart.snd := by
      simp [Wnext, TemporalGraph.TemporalWalk.endVertex?,
        TemporalGraph.TemporalWalk.endVisit?, nextVisit]
    have hWnext_within : Wnext.IsWithin startTime nextTime := by
      intro visit hvisit
      have hmem : visit ∈ W.visits ∨ visit = nextVisit := by
        simpa [Wnext] using hvisit
      rcases hmem with h_old | rfl
      · obtain ⟨hlower, hupper⟩ := hWwithin visit h_old
        exact ⟨hlower, by omega⟩
      · simp only [nextVisit]
        exact ⟨by omega, le_rfl⟩
    have hdart_end_next : dart.snd ∈ Rnext :=
      ⟨start, hstart, Wnext, hWnext_start, hWnext_end, hWnext_within⟩
    exact ⟨dart.snd, hdart_end_next, hdart_end⟩

end Lax623795Proofs
