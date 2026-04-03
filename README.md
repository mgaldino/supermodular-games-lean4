# SupermodularGames

A Lean 4 library for formally verifying results in games with strategic complementarities (supermodular games).

**Build status**: Passing | **Sorry count**: 0 | **Custom axioms**: 0 | **Lean**: 4.29.0 | **Mathlib**: v4.29.0

## Overview

Games with strategic complementarities arise across economics and political science: coordination games, club formation, treaty ratification, oligopoly with complementary goods. These games share a common mathematical backbone:

1. Action spaces form a lattice
2. Payoffs exhibit *increasing differences* (raising your action is more valuable when others raise theirs)
3. Best-response maps are monotone
4. Tarski's fixed point theorem guarantees equilibrium existence
5. The central question is: **when is the equilibrium unique vs. multiple?**

This library provides the formal infrastructure for steps 3-5, so that each new application only needs to define its game (step 1) and verify increasing differences (step 2).

## Modules

### Core

| File | Theorems | Description |
|------|----------|-------------|
| `Core/Defs.lean` | 11 | Increasing differences, Tarski existence, extremal equilibria (lfp/gfp), Topkis monotone comparative statics |

### Uniqueness (when lfp = gfp)

| File | Theorems | Description |
|------|----------|-------------|
| `Uniqueness/SingleCrossing.lean` | 5 | Gap function f(x)-x strictly decreasing implies unique fixed point. Sufficient condition: derivative < 1. |
| `Uniqueness/Laplacian.lean` | 3 | Unique root of strictly monotone CDF equations. Global games uniqueness under uniform prior. |

### Multiplicity (when lfp < gfp)

| File | Theorems | Description |
|------|----------|-------------|
| `Multiplicity/TippingPoints.lean` | 4 | Existence of 2 and 3 fixed points from boundary/oscillation conditions. |
| `Multiplicity/SShape.lean` | 3 | S-shaped best response (derivative > 1 in middle region) generates three fixed points. |
| `Multiplicity/Bifurcation.lean` | 3 | Parametric bifurcation: IVT for critical threshold, pitchfork from steep fixed point. |

### Applications

| File | Theorems | Description |
|------|----------|-------------|
| `Applications/BinaryAction.lean` | 1 | Participation rate definition for binary-action coordination games. |
| `Applications/GlobalGames.lean` | 8 | Noise CDF properties, unique coordination cutoff, participation rate strictly decreasing in noise, unique noise threshold. |
| `Applications/MeanField.lean` | 5 | Mean-field game structure, equilibrium existence, uniqueness (anti-gap), three equilibria. |

**Total: 9 files, 43 theorems/definitions, 0 sorry, 0 custom axioms.**

## Usage

### As a dependency

Add to your project's `lakefile.toml`:

```toml
[[require]]
name = "SupermodularGames"
git = "https://github.com/mgaldino/supermodular-games-lean4"
rev = "main"
```

### Building from source

```bash
git clone https://github.com/mgaldino/supermodular-games-lean4.git
cd supermodular-games-lean4
lake update && lake exe cache get
lake build
```

### Workflow for a new game

```lean
import SupermodularGames

-- 1. Define your game's payoff (GAME-SPECIFIC)
def my_payoff (a_i s : ℝ) : ℝ := ...

-- 2. Prove increasing differences (GAME-SPECIFIC)
theorem my_game_supermodular : HasIncreasingDifferences my_payoff := by ...

-- 3. Construct monotone best-response and apply Tarski (LIBRARY)
def my_BR : α →o α := ...
#check tarski_equilibrium_exists my_BR          -- equilibrium exists
#check fp_between_extremals my_BR               -- all equilibria bounded

-- 4. Uniqueness or multiplicity? (LIBRARY)
#check unique_fp_of_deriv_lt_one                -- unique if BR slope < 1
#check three_fp_of_s_shape                       -- three if S-shaped BR
#check pitchfork_from_steep_fp                   -- bifurcation mechanism

-- 5. Comparative statics (LIBRARY)
#check lfp_monotone_in_param                     -- Topkis: param up → eq up
```

## Key theorems

### Existence

- **`tarski_equilibrium_exists`**: Monotone self-map on a complete lattice has a fixed point.
- **`least_le_greatest`**: The least equilibrium is below the greatest.
- **`fp_between_extremals`**: Every equilibrium lies between lfp and gfp.

### Uniqueness

- **`unique_fp_of_strict_single_crossing`**: If f(x)-x is strictly decreasing on [a,b], there is exactly one fixed point.
- **`unique_fp_of_deriv_lt_one`**: If f'(x) < 1 everywhere on (a,b), there is exactly one fixed point.
- **`laplacian_unique_cutoff`**: Under a symmetric strictly monotone CDF, the Laplacian indifference equation has a unique root.

### Multiplicity

- **`three_fp_of_s_shape`**: If f dips below the diagonal at some interior point and rises above at another, there are (at least) three fixed points.
- **`pitchfork_from_steep_fp`**: A fixed point with f' > 1 in a neighborhood, combined with appropriate boundary conditions, generates exactly three fixed points.
- **`bifurcation_threshold_exists`**: If a stability parameter crosses the critical value 1, IVT gives the bifurcation point.

### Comparative statics

- **`lfp_monotone_in_param`**: If f_t is pointwise increasing in t, then lfp(f_t) is increasing in t.
- **`gfp_monotone_in_param`**: Same for the greatest fixed point.
- **`participationRate_strictAntiOn`**: In global games, equilibrium participation is strictly decreasing in signal noise.
- **`noise_threshold_exists_unique`**: There exists a unique noise level separating coordination success from failure.

## References

- Topkis, D. M. (1978). Minimizing a submodular function on a lattice. *Operations Research*, 26(2), 305-321.
- Milgrom, P. & Roberts, J. (1990). Rationalizability, learning, and equilibrium in games with strategic complementarities. *Econometrica*, 58(6), 1255-1277.
- Vives, X. (1990). Nash equilibrium with strategic complementarities. *Journal of Mathematical Economics*, 19(3), 305-321.
- Morris, S. & Shin, H. S. (2003). Global games: Theory and applications. In M. Dewatripont, L. P. Hansen, & S. J. Turnovsky (Eds.), *Advances in Economics and Econometrics: Theory and Applications, Eighth World Congress, Volume 1* (pp. 56-114). Cambridge University Press.
- Brock, W. A. & Durlauf, S. N. (2001). Discrete choice with social interactions. *Review of Economic Studies*, 68(2), 235-260.

## License

Apache 2.0. See [LICENSE](LICENSE).
