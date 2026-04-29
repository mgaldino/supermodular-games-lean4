/-
  One-Round Bargaining with Outside Option

  Game:
  - Proposer offers x ∈ ℝ (proposer's share of pie of size 1)
  - Responder has outside option v (payoff from rejection)
  - Accept: proposer gets x, responder gets 1-x
  - Reject: proposer gets 0, responder gets v

  Main result (spe_offer): in any SPE, the proposer captures exactly 1-v.
  The responder gets exactly their outside option — no more, no less.

  The ultimatum game is the special case v = 0.
  For Rubinstein bargaining, v = δ · (proposer's SPE share in the subgame),
  giving the backward induction step that the recursive formalization builds upon.
-/

import Mathlib

-- ===========================================================================
-- Definitions
-- ===========================================================================

/-- Responder sequential rationality with outside option v.
    The responder accepts offer x iff their share (1-x) weakly exceeds
    the rejection payoff v. Formally:
    - accepts only when profitable: x ∈ A → 1-x ≥ v
    - rejects only when not profitable: x ∉ A → 1-x ≤ v -/
def ResponderRational (accept : ℝ → Prop) (v : ℝ) : Prop :=
  (∀ x, accept x → 1 - x ≥ v) ∧
  (∀ x, ¬ accept x → 1 - x ≤ v)

/-- Proposer optimality given the responder's acceptance rule.
    The proposer's offer must be:
    (1) accepted by the responder
    (2) at least as high as any other accepted offer
    (3) weakly better than getting rejected (payoff 0) -/
def ProposerOptimal (offer : ℝ) (accept : ℝ → Prop) : Prop :=
  accept offer ∧ (∀ x, accept x → x ≤ offer) ∧ 0 ≤ offer

/-- Subgame perfect equilibrium: the responder is sequentially rational
    and the proposer plays a best response. -/
def IsSPE (offer : ℝ) (accept : ℝ → Prop) (v : ℝ) : Prop :=
  ResponderRational accept v ∧ ProposerOptimal offer accept

-- ===========================================================================
-- Main theorem: SPE offer = 1 - v
-- ===========================================================================

/-- In any SPE, the proposer captures exactly 1-v.

    Proof sketch:
    - Upper bound: the offer is accepted, so 1-offer ≥ v, hence offer ≤ 1-v.
    - Lower bound: by contradiction. If offer < 1-v, the midpoint
      m = (offer + (1-v))/2 satisfies offer < m < 1-v. Since m < 1-v,
      the responder must accept m (otherwise 1-m > v, contradicting
      sequential rationality). But m > offer contradicts proposer optimality. -/
theorem spe_offer (offer : ℝ) (accept : ℝ → Prop) (v : ℝ)
    (h : IsSPE offer accept v) : offer = 1 - v := by
  obtain ⟨⟨h_acc, h_rej⟩, h_in, h_max, _⟩ := h
  have h_le : offer ≤ 1 - v := by linarith [h_acc offer h_in]
  have h_ge : offer ≥ 1 - v := by
    by_contra hlt
    push Not at hlt
    have : accept ((offer + (1 - v)) / 2) := by
      by_contra hx_nin
      linarith [h_rej _ hx_nin]
    linarith [h_max _ this]
  linarith

/-- In any SPE, the responder gets exactly their outside option. -/
theorem spe_responder_payoff (offer : ℝ) (accept : ℝ → Prop) (v : ℝ)
    (h : IsSPE offer accept v) : 1 - offer = v := by
  linarith [spe_offer offer accept v h]

-- ===========================================================================
-- Existence
-- ===========================================================================

/-- An SPE exists when the outside option is feasible (v ∈ [0,1]).
    Construction: accept = {x | x ≤ 1-v}, offer = 1-v. -/
theorem spe_exists (v : ℝ) (_ : 0 ≤ v) (hv1 : v ≤ 1) :
    ∃ offer accept, IsSPE offer accept v := by
  use 1 - v, fun x => x ≤ 1 - v
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx; linarith
  · intro x hx; push Not at hx; linarith
  · linarith
  · intro x hx; exact hx
  · linarith

-- ===========================================================================
-- Ultimatum game (v = 0)
-- ===========================================================================

/-- In the ultimatum game (outside option = 0), the proposer takes everything. -/
theorem ultimatum_offer (offer : ℝ) (accept : ℝ → Prop)
    (h : IsSPE offer accept 0) : offer = 1 := by
  linarith [spe_offer offer accept 0 h]

/-- In the ultimatum game, the responder gets zero. -/
theorem ultimatum_responder (offer : ℝ) (accept : ℝ → Prop)
    (h : IsSPE offer accept 0) : 1 - offer = 0 := by
  linarith [ultimatum_offer offer accept h]
