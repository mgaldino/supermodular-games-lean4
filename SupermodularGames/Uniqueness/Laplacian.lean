/-
  SupermodularGames.Uniqueness.Laplacian

  Laplacian property for global games: under a noise CDF that is
  strictly monotone and continuous with limits 0 and 1, the
  indifference equation 1 − F((ω − ω₀)/σ) = target has a unique
  solution ω for any target ∈ (0,1).

  This is the key uniqueness result for threshold equilibria in
  global games. Under a uniform (diffuse) prior, each player's
  posterior probability of the state exceeding a threshold is
  monotone in the signal, so the indifference condition pins down
  a unique cutoff.

  The proof decomposes into:
  1. A strictly monotone continuous CDF hits every value in (0,1)
     exactly once (IVT + injectivity).
  2. The affine transformation ω ↦ (ω − ω₀)/σ is a bijection,
     so the unique root transfers to the ω-space.

  References:
  - Morris & Shin (2003), "Global games: theory and applications"
  - Carlsson & van Damme (1993), "Global games and equilibrium selection"

  Papers served: IA-dem (Lemmas 1-2), Strategic Ratification
-/

import Mathlib

noncomputable section

open Filter Set

/-! ## 1. Noise CDF structure -/

/-- A noise CDF: a strictly monotone, continuous distribution function
    with the standard limits F(x) → 0 as x → −∞ and F(x) → 1 as x → +∞.
    Strict monotonicity (not just monotonicity) is essential for
    uniqueness — flat segments would create intervals of solutions. -/
structure NoiseCDF where
  F : ℝ → ℝ
  strict_mono : StrictMono F
  cont : Continuous F
  tendsto_bot : Tendsto F atBot (nhds 0)
  tendsto_top : Tendsto F atTop (nhds 1)

/-! ## 2. Unique root of a strict CDF -/

/-- A strictly monotone continuous CDF hits every value in (0,1)
    exactly once.
    Existence: IVT on ℝ (preconnected) using limit behavior.
    Uniqueness: strict monotonicity implies injectivity. -/
theorem unique_root_of_strictMono_cdf (cdf : NoiseCDF) (y : ℝ)
    (hy : 0 < y ∧ y < 1) :
    ∃! x, cdf.F x = y := by
  apply existsUnique_of_exists_of_unique
  · -- Existence via IVT on ℝ
    exact intermediate_value_univ₂_eventually₂
      cdf.cont continuous_const
      (cdf.tendsto_bot.eventually_le_const hy.1)
      (cdf.tendsto_top.eventually_const_le hy.2)
  · -- Uniqueness via strict monotonicity
    intro x₁ x₂ h₁ h₂
    exact cdf.strict_mono.injective (h₁.trans h₂.symm)

/-! ## 3. Laplacian unique cutoff -/

/-- **Laplacian uniqueness theorem.**
    For a noise CDF F, center ω₀, scale σ > 0, and any target ∈ (0,1),
    the indifference equation 1 − F((ω − ω₀)/σ) = target has exactly
    one solution ω.

    This is the formal content of the "Laplacian property": under a
    diffuse prior, the equilibrium cutoff is uniquely determined by
    the indifference condition. -/
theorem laplacian_unique_cutoff (cdf : NoiseCDF) (ω₀ : ℝ) (target : ℝ)
    (ht : 0 < target ∧ target < 1) (σ : ℝ) (hσ : σ > 0) :
    ∃! ω, 1 - cdf.F ((ω - ω₀) / σ) = target := by
  -- Reduce to F(z) = 1 - target
  have h_compl : 0 < 1 - target ∧ 1 - target < 1 := ⟨by linarith, by linarith⟩
  obtain ⟨x₀, hx₀, hx₀_uniq⟩ := unique_root_of_strictMono_cdf cdf (1 - target) h_compl
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  refine ⟨σ * x₀ + ω₀, ?_, ?_⟩
  · -- Verify: 1 - F((σ * x₀ + ω₀ - ω₀) / σ) = target
    change 1 - cdf.F ((σ * x₀ + ω₀ - ω₀) / σ) = target
    rw [add_sub_cancel_right, mul_div_cancel_left₀ x₀ hσ_ne, hx₀]
    ring
  · -- Uniqueness: any solution ω must equal σ * x₀ + ω₀
    intro ω hω
    have h_eq : cdf.F ((ω - ω₀) / σ) = 1 - target := by linarith
    have h_root := hx₀_uniq ((ω - ω₀) / σ) h_eq
    -- (ω - ω₀) / σ = x₀  ⟹  ω = σ * x₀ + ω₀
    field_simp at h_root
    linarith

end
