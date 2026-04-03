/-
  SupermodularGames.Applications.GlobalGames

  Global games: coordination under incomplete information.

  This module formalizes the two core results (Lemmas 1-2) that
  drive the "crossed fragility" mechanism in the IA-dem paper:

  **Lemma 1** (unique cutoff): Under the Laplacian property, the
  indifference equation uniquely pins down the equilibrium cutoff.
  This is a direct application of `laplacian_unique_cutoff`.

  **Lemma 2** (noise comparative statics): The participation rate
  π(σ) = 1 − F(gap/σ) is strictly decreasing in noise σ when the
  realized state exceeds the fundamental threshold (gap < 0).
  This implies existence of a unique noise threshold σ̂ separating
  coordination success from failure.

  References:
  - Morris & Shin (2003), "Global games: theory and applications"
  - Carlsson & van Damme (1993), "Global games and equilibrium selection"

  Papers served: IA-dem (Lemmas 1-2), Strategic Ratification
-/

import SupermodularGames.Applications.BinaryAction

noncomputable section

open Set Filter

/-! ## 1. NoiseCDF range bounds -/

/-- F(x) ≤ 1 for all x: a CDF is bounded above by 1. -/
theorem NoiseCDF.F_le_one (cdf : NoiseCDF) (x : ℝ) : cdf.F x ≤ 1 :=
  cdf.strict_mono.monotone.ge_of_tendsto cdf.tendsto_top x

/-- 0 ≤ F(x) for all x: a CDF is nonneg. -/
theorem NoiseCDF.F_nonneg (cdf : NoiseCDF) (x : ℝ) : 0 ≤ cdf.F x :=
  cdf.strict_mono.monotone.le_of_tendsto cdf.tendsto_bot x

/-- F(x) < 1 for all x. Strict bound from strict monotonicity:
    if F(x) = 1, then F(x+1) > 1, contradicting F ≤ 1. -/
theorem NoiseCDF.F_lt_one (cdf : NoiseCDF) (x : ℝ) : cdf.F x < 1 := by
  rcases lt_or_eq_of_le (cdf.F_le_one x) with h | h
  · exact h
  · exfalso
    have := cdf.strict_mono (show x < x + 1 by linarith)
    linarith [cdf.F_le_one (x + 1)]

/-- 0 < F(x) for all x. Strict bound from strict monotonicity:
    if F(x) = 0, then F(x−1) < 0, contradicting F ≥ 0. -/
theorem NoiseCDF.F_pos (cdf : NoiseCDF) (x : ℝ) : 0 < cdf.F x := by
  rcases lt_or_eq_of_le (cdf.F_nonneg x) with h | h
  · exact h
  · exfalso
    have := cdf.strict_mono (show x - 1 < x by linarith)
    linarith [cdf.F_nonneg (x - 1)]

/-! ## 2. Lemma 1: Unique equilibrium cutoff -/

/-- **Lemma 1 (unique cutoff).** In a coordination game with benefit b,
    cost m, noise CDF F, center ω₀, and noise scale σ, the indifference
    equation 1 − F((ω − ω₀)/σ) = m/(b+m) has a unique solution ω.
    This is a direct application of the Laplacian uniqueness theorem. -/
theorem coordination_unique_cutoff (cdf : NoiseCDF)
    (b m : ℝ) (hb : 0 < b) (hm : 0 < m)
    (ω₀ : ℝ) (σ : ℝ) (hσ : σ > 0) :
    ∃! ω, 1 - cdf.F ((ω - ω₀) / σ) = m / (b + m) :=
  laplacian_unique_cutoff cdf ω₀ (m / (b + m))
    ⟨div_pos hm (by linarith), (div_lt_one (by linarith : (0 : ℝ) < b + m)).mpr (by linarith)⟩ σ hσ

/-! ## 3. Lemma 2: Participation rate decreasing in noise -/

/-- When the gap is negative, σ ↦ gap/σ is strictly increasing
    on (0,∞). Intuitively: dividing a negative number by a smaller
    positive number gives a more negative result. -/
theorem neg_div_strictMonoOn_Ioi (c : ℝ) (hc : c < 0) :
    StrictMonoOn (fun σ => c / σ) (Ioi 0) := by
  intro σ₁ hσ₁ σ₂ hσ₂ hlt
  rw [div_lt_div_iff₀ (mem_Ioi.mp hσ₁) (mem_Ioi.mp hσ₂)]
  nlinarith [mem_Ioi.mp hσ₁, mem_Ioi.mp hσ₂]

/-- **Lemma 2 (noise comparative statics).** The participation rate
    π(σ) = 1 − F(gap/σ) is strictly decreasing in σ on (0,∞) when
    the gap is negative (realized state exceeds threshold).

    As noise increases, coordination becomes harder:
    - σ → 0⁺: gap/σ → −∞, F → 0, π → 1 (perfect coordination)
    - σ → ∞:  gap/σ → 0, F → F(0), π → 1−F(0) (random) -/
theorem participationRate_strictAntiOn (cdf : NoiseCDF) (gap : ℝ)
    (hgap : gap < 0) :
    StrictAntiOn (fun σ => participationRate cdf gap σ) (Ioi 0) := by
  intro σ₁ hσ₁ σ₂ hσ₂ hlt
  unfold participationRate
  exact sub_lt_sub_left
    (cdf.strict_mono.comp_strictMonoOn (neg_div_strictMonoOn_Ioi gap hgap)
      hσ₁ hσ₂ hlt) 1

/-! ## 4. Noise threshold -/

/-- **Noise threshold existence and uniqueness.** There is a unique
    σ̂ > 0 at which the participation rate equals the critical mass π̄.

    Hypotheses:
    - gap < 0: realized state exceeds the coordination threshold
    - 0 < π̄ < 1: critical mass is a proper fraction
    - 1 − π̄ < F(0): the critical mass is achievable (for symmetric
      CDF with F(0) = 1/2, this is π̄ > 1/2)

    The proof constructs σ̂ = gap / z where z is the unique point
    with F(z) = 1 − π̄, avoiding all limit/filter arguments. -/
theorem noise_threshold_exists_unique (cdf : NoiseCDF) (gap : ℝ)
    (hgap : gap < 0) (π_bar : ℝ) (hπ_pos : 0 < π_bar) (hπ_lt : π_bar < 1)
    (hπ_achievable : 1 - π_bar < cdf.F 0) :
    ∃! σ ∈ Ioi (0 : ℝ), participationRate cdf gap σ = π_bar := by
  -- Step 1: Find unique z with F(z) = 1 - π_bar
  have h_range : 0 < 1 - π_bar ∧ 1 - π_bar < 1 := ⟨by linarith, by linarith⟩
  obtain ⟨z, hz_eq, hz_uniq⟩ := unique_root_of_strictMono_cdf cdf (1 - π_bar) h_range
  -- Step 2: z < 0 (since F(z) = 1 - π_bar < F(0))
  have hz_neg : z < 0 := by
    rwa [← cdf.strict_mono.lt_iff_lt, hz_eq]
  -- Step 3: σ̂ = gap / z > 0
  have hσ_pos : gap / z ∈ Ioi (0 : ℝ) :=
    mem_Ioi.mpr (div_pos_of_neg_of_neg hgap hz_neg)
  -- Step 4: participationRate at σ̂ = π_bar
  have hπ_eq : participationRate cdf gap (gap / z) = π_bar := by
    unfold participationRate
    rw [div_div_cancel₀ (ne_of_lt hgap), hz_eq]
    ring
  -- Step 5: Combine existence and uniqueness
  refine ⟨gap / z, ⟨hσ_pos, hπ_eq⟩, ?_⟩
  rintro σ' ⟨hσ'_pos, hπ'_eq⟩
  exact (participationRate_strictAntiOn cdf gap hgap).injOn
    hσ'_pos hσ_pos (hπ'_eq.trans hπ_eq.symm)

end
