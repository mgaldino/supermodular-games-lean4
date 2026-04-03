/-
  SupermodularGames.Applications.BinaryAction

  Binary-action coordination games: threshold strategies and
  participation rates.

  In a coordination game with binary actions (participate / abstain),
  any monotone strategy is a threshold strategy: player i participates
  iff their signal x_i exceeds some cutoff s*.  The participation rate
  — the fraction of players who participate given noise scale σ and
  a gap between the fundamental threshold and the realized state —
  is the key observable that determines coordination success.

  References:
  - Morris & Shin (2003), "Global games: theory and applications"
  - Carlsson & van Damme (1993), "Global games and equilibrium selection"

  Papers served: IA-dem (Lemmas 1-2), Strategic Ratification
-/

import SupermodularGames.Uniqueness.Laplacian

noncomputable section

open Set

/-! ## Participation rate -/

/-- The participation rate in a binary-action coordination game.
    Given a noise CDF F, a gap = ω* − ω₀ (fundamental threshold minus
    realized state), and noise scale σ > 0, the fraction of players
    whose signal exceeds the threshold ω* is 1 − F(gap/σ).

    When gap < 0 (the realized state exceeds the threshold), most
    players participate; when gap > 0, few do. -/
def participationRate (cdf : NoiseCDF) (gap : ℝ) (σ : ℝ) : ℝ :=
  1 - cdf.F (gap / σ)

end
