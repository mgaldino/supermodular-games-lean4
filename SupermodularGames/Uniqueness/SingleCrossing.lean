/-
  SupermodularGames.Uniqueness.SingleCrossing

  Single-crossing criterion for uniqueness of fixed points.

  If f : [a,b] → [a,b] is continuous, monotone, and the "gap" function
  g(x) = f(x) − x is strictly decreasing, then f has exactly one fixed
  point in [a,b].

  Intuition: the gap g(x) = f(x) − x measures how far f is above the
  diagonal. Strictly decreasing gap means f crosses the diagonal at most
  once; continuity + self-map guarantee at least one crossing (IVT).
  Combined: exactly one.

  This is the core uniqueness engine for supermodular games where the
  best-response slope is everywhere < 1 (contraction-like, but we do
  not require Lipschitz — only that the gap is strictly anti-monotone).

  References:
  - Milgrom & Roberts (1990), "Rationalizability, learning, and
    equilibrium in games with strategic complementarities"
  - Vives (1990), "Nash equilibrium with strategic complementarities"
  - Topkis (1998), Supermodularity and Complementarity, §4.2

  Papers served: IA-dem (via Laplacian.lean), Strategic Ratification (λ < 0)
-/

import Mathlib

noncomputable section

open Set

/-! ## 1. Existence: continuous self-map on [a,b] has a fixed point -/

/-- A continuous function mapping [a,b] into itself has a fixed point.
    This is the 1-dimensional Brouwer fixed point theorem, proved via
    the intermediate value theorem applied to g(x) = f(x) − x. -/
theorem exists_fp_of_continuous_self_map
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf_maps : MapsTo f (Icc a b) (Icc a b))
    (hf_cont : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, f c = c := by
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr hab
  have h_lo : a ≤ f a := (hf_maps ha_mem).1
  have h_hi : f b ≤ b := (hf_maps hb_mem).2
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    isPreconnected_Icc.intermediate_value₂ ha_mem hb_mem
      continuousOn_id hf_cont h_lo h_hi
  exact ⟨c, hc_mem, hc_eq.symm⟩

/-! ## 2. Uniqueness: strict single crossing ⟹ at most one fixed point -/

/-- If g(x) = f(x) − x is strictly anti-monotone on [a,b], then f has
    at most one fixed point in [a,b].
    Proof: two distinct fixed points x₁ < x₂ give g(x₁) = g(x₂) = 0,
    contradicting strict decrease (which requires g(x₂) < g(x₁)). -/
theorem at_most_one_fp_of_strict_anti_gap
    (f : ℝ → ℝ) (a b : ℝ)
    (h_cross : StrictAntiOn (fun x => f x - x) (Icc a b)) :
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b,
      f x₁ = x₁ → f x₂ = x₂ → x₁ = x₂ := by
  intro x₁ hx₁ x₂ hx₂ hfx₁ hfx₂
  by_contra hne
  have h1 : f x₁ - x₁ = 0 := sub_eq_zero.mpr hfx₁
  have h2 : f x₂ - x₂ = 0 := sub_eq_zero.mpr hfx₂
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (h_cross hx₁ hx₂ h) (by linarith)
  · exact absurd (h_cross hx₂ hx₁ h) (by linarith)

/-! ## 3. Main theorem: exactly one fixed point -/

/-- **Single-crossing uniqueness theorem.**
    If f : [a,b] → [a,b] is continuous, monotone, and the gap function
    g(x) = f(x) − x is strictly decreasing, then f has exactly one
    fixed point in [a,b].

    Note: MonotoneOn is not needed for this proof (existence uses only
    continuity + self-map; uniqueness uses only StrictAntiOn of the gap).
    We include it because in all downstream applications the best-response
    is monotone, and carrying the hypothesis avoids re-proving it later. -/
theorem unique_fp_of_strict_single_crossing
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (_hf_mono : MonotoneOn f (Icc a b))
    (hf_maps : MapsTo f (Icc a b) (Icc a b))
    (hf_cont : ContinuousOn f (Icc a b))
    (h_cross : StrictAntiOn (fun x => f x - x) (Icc a b)) :
    ∃! x ∈ Icc a b, f x = x := by
  obtain ⟨c, hc_mem, hc_fp⟩ :=
    exists_fp_of_continuous_self_map f a b (le_of_lt hab) hf_maps hf_cont
  exact ⟨c, ⟨hc_mem, hc_fp⟩,
    fun y ⟨hy_mem, hy_fp⟩ =>
      at_most_one_fp_of_strict_anti_gap f a b h_cross y hy_mem c hc_mem hy_fp hc_fp⟩

/-! ## 4. Sufficient condition: derivative < 1 implies strict single crossing -/

/-- If f is differentiable on (a,b) with f'(x) < 1 everywhere, then
    the gap g(x) = f(x) − x is strictly decreasing on [a,b].
    This is the standard way to verify the single-crossing condition:
    "the best-response slope is everywhere below 1." -/
theorem strictAntiOn_gap_of_deriv_lt_one
    (f : ℝ → ℝ) (a b : ℝ)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf_deriv : ∀ x ∈ Ioo a b, deriv f x < 1) :
    StrictAntiOn (fun x => f x - x) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
  · exact hf_cont.sub continuousOn_id
  · intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun y => f y - y) (deriv f x - 1) x :=
      (hf_diff x hx).hasDerivAt.sub (hasDerivAt_id x)
    rw [hd.deriv]
    linarith [hf_deriv x hx]

/-- **Derivative uniqueness theorem** (convenience composition).
    If f : [a,b] → [a,b] is continuous, monotone, differentiable on (a,b),
    and f'(x) < 1 for all x ∈ (a,b), then f has exactly one fixed point
    in [a,b]. -/
theorem unique_fp_of_deriv_lt_one
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf_mono : MonotoneOn f (Icc a b))
    (hf_maps : MapsTo f (Icc a b) (Icc a b))
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hf_deriv : ∀ x ∈ Ioo a b, deriv f x < 1) :
    ∃! x ∈ Icc a b, f x = x :=
  unique_fp_of_strict_single_crossing f a b hab hf_mono hf_maps hf_cont
    (strictAntiOn_gap_of_deriv_lt_one f a b hf_cont hf_diff hf_deriv)

end
