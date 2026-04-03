# SupermodularGames — Lean 4 Library

## Propósito

Biblioteca Lean 4 para provar resultados em jogos com complementaridades estratégicas (supermodulares). Compartilhada entre múltiplos papers de pesquisa.

## Papers servidos

| Paper | Pasta | Módulos usados |
|---|---|---|
| IA-dem | Papers/IA-dem/ | Core + Uniqueness + Applications/GlobalGames |
| DC Estático | Papers/LivreDocencia/dc_statico/ | Core + Multiplicity + Applications/MeanField |
| DC Cross-Domain | Papers/LivreDocencia/dc_cross_domain/ | Core + Multiplicity + ComparativeStatics |
| Strategic Ratification | Papers/LivreDocencia/strategic_ratification/ | Core + Uniqueness + Multiplicity + Applications/MeanField |

## Estrutura

```
SupermodularGames/
├── Core/                  — Increasing differences, Tarski, extremal equilibria
├── Uniqueness/            — Quando lfp = gfp (contraction, single-crossing, Laplacian)
├── Multiplicity/          — Quando lfp < gfp (S-shape, bifurcation, tipping)
├── ComparativeStatics/    — Topkis, monotone CS paramétrico
└── Applications/          — BinaryAction, MeanField, GlobalGames
```

## Build

```bash
lake build
```

Primeira vez: `lake update && lake exe cache get` para baixar Mathlib.

## Convenções

- `import Mathlib` (monolítico)
- `noncomputable section` para definições com divisão
- Hipóteses explícitas em cada teorema (sem `variable` blocks)
- Táticas preferidas: `linarith`, `nlinarith`, `field_simp`, `ring`, `positivity`
- Cada arquivo auto-contido com docstring no topo (propósito, referências, papers servidos)

## Como papers importam esta biblioteca

No `lakefile.toml` do paper:
```toml
[[require]]
name = "SupermodularGames"
path = "../../SupermodularGames"  # ajustar caminho relativo
```

## Faseamento

1. Core/ + Uniqueness/ → serve IA-dem (Lemmas 1-2)
2. Multiplicity/ → serve DC (P3-P4)
3. ComparativeStatics/ → serve todos
4. Applications/ → especializações por paper
