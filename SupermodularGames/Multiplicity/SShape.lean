/-
  SupermodularGames.Multiplicity.SShape

  S-shaped best-response maps and their fixed-point multiplicity.

  An S-shaped map f : [0,1] → [0,1] is one that starts above the
  diagonal (f(0) > 0), ends below it (f(1) < 1), and has an interior
  region where the slope exceeds 1. This creates the gap oscillation
  pattern (+ → − → + → −) that `exists_three_fp` (TippingPoints.lean)
  uses to produce three distinct fixed points.

  The derivative-based results here are duals of the uniqueness results
  in SingleCrossing.lean: there, f'(x) < 1 everywhere gives a strictly
  decreasing gap (unique FP); here, f'(x) > 1 on some interval gives
  a strictly increasing gap segment (multiple FP).

  References:
  - Brock & Durlauf (2001), "Discrete choice with social interactions"
  - Glaeser, Sacerdote & Scheinkman (1996), "Crime and social interactions"

  Papers served: DC Estático (P4 bifurcation), Strategic Ratification (λ > 0)
-/

import SupermodularGames.Multiplicity.TippingPoints

noncomputable section

open Set

/-! ## 1. Strictly increasing gap from derivative > 1 -/

/-- If f is differentiable on (a,b) with f'(x) > 1 everywhere, then
    the gap g(x) = f(x) − x is strictly increasing on [a,b].

    This is the exact dual of `strictAntiOn_gap_of_deriv_lt_one`
    (SingleCrossing.lean): slope above 1 means the function pulls
    away from the diagonal, while slope below 1 means it converges. -/
theorem strictMonoOn_gap_of_deriv_gt_one
    (f : ℝ → ℝ) (a b : ℝ)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf_deriv : ∀ x ∈ Ioo a b, deriv f x > 1) :
    StrictMonoOn (fun x => f x - x) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · exact hf_cont.sub continuousOn_id
  · intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun y => f y - y) (deriv f x - 1) x :=
      (hf_diff x hx).hasDerivAt.sub (hasDerivAt_id x)
    rw [hd.deriv]
    linarith [hf_deriv x hx]

/-! ## 2. Steep region pushes above diagonal -/

/-- If f has a fixed point at a (f(a) = a) and f'(x) > 1 on (a,b),
    then f(b) > b. Intuitively: starting on the diagonal, a slope
    above 1 pulls the function above it.

    This is the mechanism by which a "steep" best-response creates
    the gap sign change needed for multiplicity. -/
theorem above_diagonal_after_fp_and_steep
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfa : f a = a)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf_deriv : ∀ x ∈ Ioo a b, deriv f x > 1) :
    f b > b := by
  have h_strict_mono := strictMonoOn_gap_of_deriv_gt_one f a b hf_cont hf_diff hf_deriv
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr (le_of_lt hab)
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr (le_of_lt hab)
  have h_gap_a : f a - a = 0 := sub_eq_zero.mpr hfa
  have h_gap_pos := h_strict_mono ha_mem hb_mem hab
  linarith

/-! ## 3. Three fixed points from S-shape on [0,1] -/

/-- **S-shape multiplicity theorem.**
    If f : [0,1] → [0,1] is continuous, f(0) > 0 (above diagonal at
    the origin), f(1) < 1 (below diagonal at 1), and there exist
    interior points a < b where f(a) < a and f(b) > b, then f has
    at least three distinct fixed points.

    The four gap conditions form the oscillation pattern + → − → + → −:
    - gap(0) = f(0) > 0      (above diagonal)
    - gap(a) = f(a) − a < 0  (below diagonal)
    - gap(b) = f(b) − b > 0  (above diagonal again)
    - gap(1) = f(1) − 1 < 0  (below diagonal again)

    This theorem is the formal content of "S-shaped BR implies three
    equilibria" and directly supports Proposition 4 (bifurcation) of
    the DC Estático paper. -/
theorem three_fp_of_s_shape
    (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (h_lo : 0 < f 0) (h_hi : f 1 < 1)
    (a b : ℝ) (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (hab : a < b)
    (h_below : f a < a) (h_above : f b > b) :
    ∃ x₁ x₂ x₃, x₁ ∈ Icc 0 a ∧ x₂ ∈ Icc a b ∧ x₃ ∈ Icc b 1
      ∧ f x₁ = x₁ ∧ f x₂ = x₂ ∧ f x₃ = x₃
      ∧ x₁ < x₂ ∧ x₂ < x₃ :=
  exists_three_fp f 0 a b 1
    (le_of_lt ha.1) (le_of_lt hab) (le_of_lt hb.2)
    hf_cont (le_of_lt h_lo) h_below h_above (le_of_lt h_hi)

end
