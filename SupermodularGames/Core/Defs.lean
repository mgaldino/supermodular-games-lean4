/-
  SupermodularGames.Core.Defs

  Fundamental definitions for games with strategic complementarities.

  A game has *increasing differences* when raising one player's action
  raises the marginal return to raising another player's action.
  Equivalently, u(a_high, s) - u(a_low, s) is increasing in s.

  When action spaces form a complete lattice and the best-response map
  is order-preserving, Tarski's fixed point theorem guarantees existence
  of equilibria (least and greatest). The central question across our
  papers is: when do these coincide (unique equilibrium) vs. differ
  (multiple equilibria)?

  References:
  - Topkis (1978), "Minimizing a submodular function on a lattice"
  - Milgrom & Roberts (1990), "Rationalizability, learning, and
    equilibrium in games with strategic complementarities"
  - Vives (1990), "Nash equilibrium with strategic complementarities"

  Papers served: IA-dem, DC, DC Cross-Domain, Strategic Ratification
-/

import Mathlib

noncomputable section

/-! ## 1. Increasing Differences -/

/-- A function f : α → β → ℝ has increasing differences if, for all
    a ≤ a', the map s ↦ f(a', s) - f(a, s) is monotone.
    This is the lattice-theoretic characterization of strategic
    complementarities (Topkis 1978). -/
def HasIncreasingDifferences {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β → ℝ) : Prop :=
  ∀ a a' : α, a ≤ a' → Monotone (fun s => f a' s - f a s)

/-- Equivalent formulation: for a ≤ a' and s ≤ s',
    f(a', s') - f(a, s') ≥ f(a', s) - f(a, s).
    "Raising your action is weakly more valuable when others raise theirs." -/
theorem hasIncreasingDifferences_iff {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β → ℝ) :
    HasIncreasingDifferences f ↔
      ∀ a a' : α, a ≤ a' → ∀ s s' : β, s ≤ s' →
        f a' s' - f a s' ≥ f a' s - f a s := by
  constructor
  · intro h a a' ha s s' hs
    exact h a a' ha hs
  · intro h a a' ha s s' hs
    exact h a a' ha s s' hs

/-! ## 2. Linearity implies increasing differences -/

/-- If the gain function is linear in the aggregate (as in many
    binary-action coordination games), increasing differences holds
    automatically. This covers IA-dem's participation payoff
    gain(q) = q·b - (1-q)·m = (b+m)·q - m. -/
theorem linear_has_increasing_differences
    (slope : ℝ) (intercept : ℝ) (h_slope : slope ≥ 0) :
    Monotone (fun s : ℝ => slope * s + intercept) := by
  intro s s' hss'
  linarith [mul_le_mul_of_nonneg_left hss' h_slope]

/-! ## 3. Tarski existence (thin wrapper on Mathlib) -/

/-- Equilibrium existence via Tarski's fixed point theorem.
    If BR : α →o α is a monotone self-map on a complete lattice,
    then BR has a fixed point. -/
theorem tarski_equilibrium_exists {α : Type*} [CompleteLattice α]
    (BR : α →o α) :
    ∃ a : α, BR a = a :=
  ⟨BR.lfp, BR.isFixedPt_lfp⟩

/-- The least equilibrium. -/
def leastEquilibrium {α : Type*} [CompleteLattice α] (BR : α →o α) : α :=
  BR.lfp

/-- The greatest equilibrium. -/
def greatestEquilibrium {α : Type*} [CompleteLattice α] (BR : α →o α) : α :=
  BR.gfp

/-- Least ≤ greatest. -/
theorem least_le_greatest {α : Type*} [CompleteLattice α]
    (BR : α →o α) :
    leastEquilibrium BR ≤ greatestEquilibrium BR := by
  unfold leastEquilibrium greatestEquilibrium
  apply OrderHom.lfp_le
  exact le_of_eq BR.isFixedPt_gfp

/-- Any fixed point lies between the extremals. -/
theorem fp_between_extremals {α : Type*} [CompleteLattice α]
    (BR : α →o α) (a : α) (ha : BR a = a) :
    leastEquilibrium BR ≤ a ∧ a ≤ greatestEquilibrium BR := by
  constructor
  · exact BR.lfp_le (le_of_eq ha)
  · exact BR.le_gfp (ge_of_eq ha)

/-- The game has a unique equilibrium iff least = greatest. -/
theorem unique_iff_extremals_eq {α : Type*} [CompleteLattice α]
    (BR : α →o α) :
    (∃! a : α, BR a = a) ↔
      (leastEquilibrium BR = greatestEquilibrium BR ∧
       ∀ a, BR a = a → a = leastEquilibrium BR) := by
  constructor
  · rintro ⟨a, ha, huniq⟩
    have h1 := huniq BR.lfp BR.isFixedPt_lfp
    have h2 := huniq BR.gfp BR.isFixedPt_gfp
    constructor
    · unfold leastEquilibrium greatestEquilibrium
      rw [h1, h2]
    · intro b hb
      unfold leastEquilibrium
      rw [h1]
      exact huniq b hb
  · rintro ⟨heq, huniq⟩
    exact ⟨leastEquilibrium BR, BR.isFixedPt_lfp, huniq⟩

/-! ## 4. Monotone comparative statics (Topkis) -/

/-- If f_t is pointwise monotone in parameter t, then the least
    fixed point lfp(f_t) is monotone in t.
    This is the core of Topkis (1978) / Milgrom-Roberts (1990). -/
theorem lfp_monotone_in_param {α : Type*} [CompleteLattice α]
    {T : Type*} [Preorder T]
    (f : T → α →o α)
    (hf : ∀ (t₁ t₂ : T), t₁ ≤ t₂ → ∀ a : α, f t₁ a ≤ f t₂ a) :
    Monotone (fun t => (f t).lfp) := by
  intro t₁ t₂ ht
  apply OrderHom.lfp_le
  calc f t₁ ((f t₂).lfp)
      ≤ f t₂ ((f t₂).lfp) := hf t₁ t₂ ht _
    _ = (f t₂).lfp := (f t₂).isFixedPt_lfp

/-- Same for greatest fixed point. -/
theorem gfp_monotone_in_param {α : Type*} [CompleteLattice α]
    {T : Type*} [Preorder T]
    (f : T → α →o α)
    (hf : ∀ (t₁ t₂ : T), t₁ ≤ t₂ → ∀ a : α, f t₁ a ≤ f t₂ a) :
    Monotone (fun t => (f t).gfp) := by
  intro t₁ t₂ ht
  apply OrderHom.le_gfp
  calc (f t₁).gfp
      = f t₁ ((f t₁).gfp) := (f t₁).isFixedPt_gfp.symm
    _ ≤ f t₂ ((f t₁).gfp) := hf t₁ t₂ ht _

end
