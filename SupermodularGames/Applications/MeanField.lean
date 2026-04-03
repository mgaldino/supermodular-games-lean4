/-
  SupermodularGames.Applications.MeanField

  Mean-field games: a continuum of agents with aggregate interaction.

  In a mean-field game, each agent's payoff depends on their own action
  and an aggregate statistic (e.g., the fraction of participants, the
  mean action). The equilibrium is a fixed point of the aggregate
  best-response map Φ : [0,1] → [0,1], where Φ(m) is the aggregate
  action when agents best-respond to an anticipated aggregate m.

  This module provides:
  - The `MeanFieldGame` structure bundling Φ with regularity conditions
  - Equilibrium existence (Brouwer / IVT)
  - Uniqueness wrapper (via SingleCrossing, for log-concave distributions)
  - Multiplicity wrapper (via SShape, for bimodal distributions)

  The DC Estático paper uses this as follows:
  - P3 (uniqueness): Φ has slope < 1 everywhere under log-concavity
    → StrictAntiOn gap → unique equilibrium
  - P4 (bifurcation): under bimodal alignment, Φ becomes S-shaped
    → three equilibria via `three_fp_of_s_shape`

  References:
  - Brock & Durlauf (2001), "Discrete choice with social interactions"
  - Guimarães & Machado (2025), "Digital currencies and club formation"

  Papers served: DC Estático, DC Cross-Domain, Strategic Ratification
-/

import SupermodularGames.Multiplicity.SShape
import SupermodularGames.Uniqueness.SingleCrossing

noncomputable section

open Set

/-! ## 1. Mean-field game structure -/

/-- A mean-field game is specified by an aggregate best-response map
    Φ : [0,1] → [0,1] that is continuous. The continuity and self-map
    conditions guarantee equilibrium existence.

    In applications:
    - Φ(m) = ∫ 1{θ > θ*(ψ; m)} dF_θ dF_ψ  (DC model)
    - The "1" action space [0,1] represents the membership rate
    - MapsTo ensures Φ returns a valid membership rate -/
structure MeanFieldGame where
  Φ : ℝ → ℝ
  cont : ContinuousOn Φ (Icc 0 1)
  maps : MapsTo Φ (Icc 0 1) (Icc 0 1)

/-- A membership rate m is a mean-field equilibrium if it is in [0,1]
    and is a fixed point of the aggregate best-response map. -/
def MeanFieldEquilibrium (G : MeanFieldGame) (m : ℝ) : Prop :=
  m ∈ Icc (0 : ℝ) 1 ∧ G.Φ m = m

/-! ## 2. Equilibrium existence -/

/-- **Mean-field equilibrium existence.**
    Any mean-field game has at least one equilibrium. This follows
    directly from the 1-dimensional Brouwer fixed point theorem
    (IVT applied to g(x) = f(x) − x on [0,1]). -/
theorem meanField_equilibrium_exists (G : MeanFieldGame) :
    ∃ m, MeanFieldEquilibrium G m := by
  obtain ⟨c, hc_mem, hc_fp⟩ :=
    exists_fp_of_continuous_self_map G.Φ 0 1 zero_le_one G.maps G.cont
  exact ⟨c, hc_mem, hc_fp⟩

/-! ## 3. Uniqueness (serves P3) -/

/-- **Mean-field uniqueness.**
    If the gap g(m) = Φ(m) − m is strictly decreasing, then the
    equilibrium is unique. This is the condition satisfied when
    the alignment distribution is log-concave (P3 of DC Estático):
    log-concavity ensures the derivative of Φ is everywhere < 1,
    which makes the gap strictly decreasing. -/
theorem meanField_unique_of_strict_anti_gap (G : MeanFieldGame)
    (h_cross : StrictAntiOn (fun x => G.Φ x - x) (Icc 0 1)) :
    ∃! m ∈ Icc (0 : ℝ) 1, G.Φ m = m := by
  obtain ⟨c, hc_mem, hc_fp⟩ :=
    exists_fp_of_continuous_self_map G.Φ 0 1 zero_le_one G.maps G.cont
  exact ⟨c, ⟨hc_mem, hc_fp⟩,
    fun y ⟨hy_mem, hy_fp⟩ =>
      at_most_one_fp_of_strict_anti_gap G.Φ 0 1 h_cross y hy_mem c hc_mem hy_fp hc_fp⟩

/-! ## 4. Multiplicity (serves P4) -/

/-- **Mean-field multiplicity.**
    If Φ(0) > 0, Φ(1) < 1, and there exist interior points where Φ
    crosses below and then above the diagonal, there are at least
    three distinct equilibria.

    In the DC Estático paper, this happens when the alignment
    distribution is bimodal with polarization μ > μ*: the S-shaped
    Φ produces a low-membership equilibrium, an unstable middle,
    and a high-membership equilibrium. -/
theorem meanField_three_equilibria (G : MeanFieldGame)
    (h_lo : 0 < G.Φ 0) (h_hi : G.Φ 1 < 1)
    (a b : ℝ) (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (hab : a < b)
    (h_below : G.Φ a < a) (h_above : G.Φ b > b) :
    ∃ m₁ m₂ m₃, MeanFieldEquilibrium G m₁ ∧ MeanFieldEquilibrium G m₂
      ∧ MeanFieldEquilibrium G m₃ ∧ m₁ < m₂ ∧ m₂ < m₃ := by
  obtain ⟨x₁, x₂, x₃, hx₁_mem, hx₂_mem, hx₃_mem,
    hx₁_fp, hx₂_fp, hx₃_fp, h12, h23⟩ :=
    three_fp_of_s_shape G.Φ G.cont h_lo h_hi a b ha hb hab h_below h_above
  exact ⟨x₁, x₂, x₃,
    ⟨Icc_subset_Icc le_rfl (le_of_lt ha.2) hx₁_mem, hx₁_fp⟩,
    ⟨Icc_subset_Icc (le_of_lt ha.1) (le_of_lt hb.2) hx₂_mem, hx₂_fp⟩,
    ⟨Icc_subset_Icc (le_of_lt hb.1) le_rfl hx₃_mem, hx₃_fp⟩,
    h12, h23⟩

end
