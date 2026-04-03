/-
  SupermodularGames.Multiplicity.Bifurcation

  Parametric bifurcation: how equilibrium multiplicity emerges as a
  parameter crosses a critical threshold.

  In many coordination games, a "stability function" Γ(μ) measures
  how steep the best-response is at a symmetric fixed point. When
  Γ(μ) < 1, the fixed point is unique and stable; when Γ(μ) > 1,
  the best-response is steep enough to create an S-shape, generating
  two additional fixed points (pitchfork bifurcation).

  The key results:
  1. `bifurcation_threshold_exists`: IVT guarantees a critical μ*
     where Γ(μ*) = 1.
  2. `below_diagonal_before_fp_and_steep`: a steep region before a
     fixed point pushes f below the diagonal.
  3. `pitchfork_from_steep_fp`: a fixed point surrounded by a steep
     region, with appropriate boundary conditions, generates three
     distinct fixed points.

  References:
  - Brock & Durlauf (2001), "Discrete choice with social interactions"

  Papers served: DC Estático (P4), Strategic Ratification (λ > 0)
-/

import SupermodularGames.Multiplicity.SShape

noncomputable section

open Set

/-! ## 1. Bifurcation threshold via IVT -/

/-- **Bifurcation threshold existence.**
    If a stability function Γ is continuous and crosses the critical
    value 1 (Γ(μ₀) < 1 in the unique regime, Γ(μ₁) > 1 in the
    multiple regime), then there exists a critical parameter μ* where
    Γ(μ*) = 1 exactly.

    In the DC paper, Γ(μ) = 2β ∫ ψ² f_θ(θ₀*(ψ;μ)) f_ψ(ψ;μ) dψ
    measures how alignment heterogeneity amplifies strategic
    complementarities. The bifurcation at μ* separates the unique
    inclusive equilibrium from the three-equilibria regime. -/
theorem bifurcation_threshold_exists
    (Γ : ℝ → ℝ) (μ₀ μ₁ : ℝ) (hμ : μ₀ ≤ μ₁)
    (hΓ_cont : ContinuousOn Γ (Icc μ₀ μ₁))
    (h_stable : Γ μ₀ < 1) (h_unstable : Γ μ₁ > 1) :
    ∃ μ_star ∈ Icc μ₀ μ₁, Γ μ_star = 1 := by
  have hlo : Γ μ₀ ≤ 1 := le_of_lt h_stable
  have hhi : 1 ≤ Γ μ₁ := le_of_lt h_unstable
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (left_mem_Icc.mpr hμ) (right_mem_Icc.mpr hμ)
      hΓ_cont continuousOn_const hlo hhi
  exact ⟨c, hc_mem, hc_eq⟩

/-! ## 2. Below diagonal before a steep fixed point -/

/-- **Below diagonal before a steep fixed point.**
    If f has a fixed point at b (f(b) = b) and f'(x) > 1 for all
    x ∈ (a,b), then f(a) < a (f lies below the diagonal at a).

    This is the "left-side" companion to `above_diagonal_after_fp_and_steep`
    (SShape.lean). The gap g(x) = f(x) − x is strictly increasing on
    [a,b], so g(a) < g(b) = 0.

    Economically: a steep best-response that passes through a fixed
    point must lie below the diagonal to the left of that point. -/
theorem below_diagonal_before_fp_and_steep
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfb : f b = b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf_deriv : ∀ x ∈ Ioo a b, deriv f x > 1) :
    f a < a := by
  have h_strict_mono := strictMonoOn_gap_of_deriv_gt_one f a b hf_cont hf_diff hf_deriv
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr (le_of_lt hab)
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr (le_of_lt hab)
  have h_gap_b : f b - b = 0 := sub_eq_zero.mpr hfb
  have h_gap_lt := h_strict_mono ha_mem hb_mem hab
  linarith

/-! ## 3. Pitchfork bifurcation: steep fixed point → three equilibria -/

/-- **Pitchfork bifurcation theorem.**
    If f : [0,1] → [0,1] is continuous, has a fixed point at p,
    and the derivative exceeds 1 on a region (a,b) containing p,
    with f(0) > 0 and f(1) < 1, then f has at least three distinct
    fixed points.

    The mechanism:
    - The steep region (f' > 1) around p makes the gap strictly increasing.
    - Since gap(p) = 0, we get gap(a) < 0 (f below diagonal at a)
      and gap(b) > 0 (f above diagonal at b).
    - Combined with gap(0) > 0 and gap(1) < 0, this creates the
      oscillation pattern + → − → + → − that `three_fp_of_s_shape`
      converts into three distinct fixed points.

    This is the formal content of the pitchfork bifurcation in
    Proposition 4 of the DC Estático paper: when the alignment
    distribution is sufficiently bimodal (μ > μ*), the aggregate
    best-response becomes steep enough around the symmetric
    equilibrium to spawn two discriminatory club equilibria. -/
theorem pitchfork_from_steep_fp
    (f : ℝ → ℝ) (p a b : ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (_hp_mem : p ∈ Ioo 0 1)
    (ha_mem : a ∈ Ioo 0 p) (hb_mem : b ∈ Ioo p 1)
    (hf_fp : f p = p)
    (h_lo : 0 < f 0) (h_hi : f 1 < 1)
    (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf_deriv : ∀ x ∈ Ioo a b, deriv f x > 1) :
    ∃ x₁ x₂ x₃, x₁ ∈ Icc 0 a ∧ x₂ ∈ Icc a b ∧ x₃ ∈ Icc b 1
      ∧ f x₁ = x₁ ∧ f x₂ = x₂ ∧ f x₃ = x₃
      ∧ x₁ < x₂ ∧ x₂ < x₃ := by
  -- Step 1: steep region makes f(a) < a and f(b) > b
  have hab : a < b := lt_trans ha_mem.2 hb_mem.1
  have hf_cont_ab : ContinuousOn f (Icc a b) :=
    hf_cont.mono (Icc_subset_Icc (le_of_lt ha_mem.1) (le_of_lt hb_mem.2))
  have h_below : f a < a :=
    below_diagonal_before_fp_and_steep f a p ha_mem.2
      hf_fp
      (hf_cont_ab.mono (Icc_subset_Icc le_rfl (le_of_lt hb_mem.1)))
      (fun x hx => hf_diff x ⟨hx.1, lt_trans hx.2 hb_mem.1⟩)
      (fun x hx => hf_deriv x ⟨hx.1, lt_trans hx.2 hb_mem.1⟩)
  have h_above : f b > b :=
    above_diagonal_after_fp_and_steep f p b hb_mem.1
      hf_fp
      (hf_cont_ab.mono (Icc_subset_Icc (le_of_lt ha_mem.2) le_rfl))
      (fun x hx => hf_diff x ⟨lt_trans ha_mem.2 hx.1, hx.2⟩)
      (fun x hx => hf_deriv x ⟨lt_trans ha_mem.2 hx.1, hx.2⟩)
  -- Step 2: apply three_fp_of_s_shape
  have ha_01 : a ∈ Ioo 0 1 := ⟨ha_mem.1, lt_trans ha_mem.2 (lt_trans hb_mem.1 hb_mem.2)⟩
  have hb_01 : b ∈ Ioo 0 1 := ⟨lt_trans ha_mem.1 (lt_trans ha_mem.2 hb_mem.1), hb_mem.2⟩
  exact three_fp_of_s_shape f hf_cont h_lo h_hi a b ha_01 hb_01 hab h_below h_above

end
