/-
  SupermodularGames.Multiplicity.TippingPoints

  General results on the existence of multiple fixed points for
  continuous self-maps on closed intervals.

  When a continuous function f : [a,d] → ℝ has its "gap" g(x) = f(x) − x
  oscillating in sign — positive at some points, negative at others —
  the intermediate value theorem forces multiple zero-crossings of g,
  each giving a distinct fixed point of f.

  These results provide the structural backbone for multiplicity of
  equilibria in supermodular games. The key theorem `exists_three_fp`
  gives three distinct fixed points when the gap oscillates twice
  (+ → − → + → −), which is exactly the pattern of an S-shaped
  best-response map.

  References:
  - Milgrom & Roberts (1990), "Rationalizability, learning, and
    equilibrium in games with strategic complementarities"
  - Brock & Durlauf (2001), "Discrete choice with social interactions"

  Papers served: DC Estático (P4 bifurcation), Strategic Ratification
-/

import Mathlib

noncomputable section

open Set

/-! ## 1. Fixed point from gap sign: above then below -/

/-- **IVT for fixed points (above-below).**
    If f is continuous on [a,b] and f(a) ≥ a ("above diagonal at left")
    while f(b) ≤ b ("below diagonal at right"), then f has a fixed point
    in [a,b].

    This generalizes `exists_fp_of_continuous_self_map` (SingleCrossing.lean)
    by not requiring the full MapsTo condition — only the boundary
    inequalities needed for IVT. -/
theorem exists_fp_of_continuous_above_below
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (h_lo : a ≤ f a) (h_hi : f b ≤ b) :
    ∃ c ∈ Icc a b, f c = c := by
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      continuousOn_id hf_cont h_lo h_hi
  exact ⟨c, hc_mem, hc_eq.symm⟩

/-! ## 2. Fixed point from gap sign: below then above -/

/-- **IVT for fixed points (below-above).**
    Dual of the above: if f(a) ≤ a and f(b) ≥ b, there is a fixed
    point in [a,b]. -/
theorem exists_fp_of_continuous_below_above
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (h_lo : f a ≤ a) (h_hi : b ≤ f b) :
    ∃ c ∈ Icc a b, f c = c := by
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      hf_cont continuousOn_id h_lo h_hi
  exact ⟨c, hc_mem, hc_eq⟩

/-! ## 3. Two distinct fixed points -/

/-- **Two distinct fixed points from one gap oscillation.**
    If the gap g(x) = f(x) − x is nonneg at a, strictly negative at b,
    and nonneg at c (with a ≤ b ≤ c), then f has two distinct fixed
    points x₁ ∈ [a,b] and x₂ ∈ [b,c] with x₁ < x₂.

    The strict inequality at b (f(b) < b) is essential for distinctness:
    it ensures b itself is not a fixed point, so the fixed point in [a,b]
    must be strictly less than b, and the one in [b,c] strictly greater. -/
theorem exists_two_fp
    (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hf_cont : ContinuousOn f (Icc a c))
    (h1 : a ≤ f a) (h2 : f b < b) (h3 : c ≤ f c) :
    ∃ x₁ x₂, x₁ ∈ Icc a b ∧ x₂ ∈ Icc b c
      ∧ f x₁ = x₁ ∧ f x₂ = x₂ ∧ x₁ < x₂ := by
  -- Fixed point in [a,b]: gap goes from ≥ 0 to < 0
  have hf_cont_ab : ContinuousOn f (Icc a b) :=
    hf_cont.mono (Icc_subset_Icc le_rfl hbc)
  obtain ⟨x₁, hx₁_mem, hx₁_fp⟩ :=
    exists_fp_of_continuous_above_below f a b hab hf_cont_ab h1 (le_of_lt h2)
  -- Fixed point in [b,c]: gap goes from < 0 to ≥ 0
  have hf_cont_bc : ContinuousOn f (Icc b c) :=
    hf_cont.mono (Icc_subset_Icc hab le_rfl)
  obtain ⟨x₂, hx₂_mem, hx₂_fp⟩ :=
    exists_fp_of_continuous_below_above f b c hbc hf_cont_bc (le_of_lt h2) h3
  -- Distinctness: f(b) < b means b is not a fixed point
  have hx₁_lt_b : x₁ < b := by
    rcases lt_or_eq_of_le hx₁_mem.2 with h | h
    · exact h
    · exfalso; rw [h] at hx₁_fp; linarith
  have hb_lt_x₂ : b < x₂ := by
    rcases lt_or_eq_of_le hx₂_mem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hx₂_fp; linarith
  exact ⟨x₁, x₂, hx₁_mem, hx₂_mem, hx₁_fp, hx₂_fp, lt_trans hx₁_lt_b hb_lt_x₂⟩

/-! ## 4. Three distinct fixed points -/

/-- **Three distinct fixed points from two gap oscillations.**
    If the gap oscillates as + → − → + → −, i.e.,
    - g(a) ≥ 0  (f above diagonal)
    - g(b) < 0  (f strictly below diagonal)
    - g(c) > 0  (f strictly above diagonal)
    - g(d) ≤ 0  (f below diagonal)
    with a ≤ b ≤ c ≤ d, then IVT gives a fixed point in each of
    [a,b], [b,c], [c,d], and the strict conditions at b and c
    guarantee all three are distinct.

    This is the core multiplicity result that underpins the S-shaped
    best-response analysis in coordination games with heterogeneous
    agents. -/
theorem exists_three_fp
    (f : ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hf_cont : ContinuousOn f (Icc a d))
    (h1 : a ≤ f a) (h2 : f b < b)
    (h3 : f c > c) (h4 : f d ≤ d) :
    ∃ x₁ x₂ x₃, x₁ ∈ Icc a b ∧ x₂ ∈ Icc b c ∧ x₃ ∈ Icc c d
      ∧ f x₁ = x₁ ∧ f x₂ = x₂ ∧ f x₃ = x₃
      ∧ x₁ < x₂ ∧ x₂ < x₃ := by
  -- Continuity on sub-intervals
  have hf_cont_ab : ContinuousOn f (Icc a b) :=
    hf_cont.mono (Icc_subset_Icc le_rfl (le_trans hbc hcd))
  have hf_cont_bc : ContinuousOn f (Icc b c) :=
    hf_cont.mono (Icc_subset_Icc hab hcd)
  have hf_cont_cd : ContinuousOn f (Icc c d) :=
    hf_cont.mono (Icc_subset_Icc (le_trans hab hbc) le_rfl)
  -- Fixed point in [a,b]: gap ≥ 0 at a, < 0 at b
  obtain ⟨x₁, hx₁_mem, hx₁_fp⟩ :=
    exists_fp_of_continuous_above_below f a b hab hf_cont_ab h1 (le_of_lt h2)
  -- Fixed point in [b,c]: gap < 0 at b, > 0 at c
  obtain ⟨x₂, hx₂_mem, hx₂_fp⟩ :=
    exists_fp_of_continuous_below_above f b c hbc hf_cont_bc (le_of_lt h2) (le_of_lt h3)
  -- Fixed point in [c,d]: gap > 0 at c, ≤ 0 at d
  obtain ⟨x₃, hx₃_mem, hx₃_fp⟩ :=
    exists_fp_of_continuous_above_below f c d hcd hf_cont_cd (le_of_lt h3) h4
  -- Distinctness from strict gap conditions at b and c
  have hx₁_lt_b : x₁ < b := by
    rcases lt_or_eq_of_le hx₁_mem.2 with h | h
    · exact h
    · exfalso; rw [h] at hx₁_fp; linarith
  have hb_lt_x₂ : b < x₂ := by
    rcases lt_or_eq_of_le hx₂_mem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hx₂_fp; linarith
  have hx₂_lt_c : x₂ < c := by
    rcases lt_or_eq_of_le hx₂_mem.2 with h | h
    · exact h
    · exfalso; rw [h] at hx₂_fp; linarith
  have hc_lt_x₃ : c < x₃ := by
    rcases lt_or_eq_of_le hx₃_mem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hx₃_fp; linarith
  exact ⟨x₁, x₂, x₃, hx₁_mem, hx₂_mem, hx₃_mem,
    hx₁_fp, hx₂_fp, hx₃_fp,
    lt_trans hx₁_lt_b hb_lt_x₂, lt_trans hx₂_lt_c hc_lt_x₃⟩

end
