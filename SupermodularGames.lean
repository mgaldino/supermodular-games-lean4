-- SupermodularGames: Lean 4 library for supermodular games
--
-- A shared library for proving equilibrium existence, uniqueness,
-- multiplicity, and comparative statics in games with strategic
-- complementarities.
--
-- Papers served:
--   IA-dem (global games, coordination)
--   DC (mean-field, bifurcation)
--   DC Cross-Domain (spillover)
--   Strategic Ratification (network vs free-riding)

import SupermodularGames.Core.Defs
-- import SupermodularGames.Core.Tarski
-- import SupermodularGames.Core.ExtremalEquilibria
import SupermodularGames.Uniqueness.SingleCrossing
import SupermodularGames.Uniqueness.Laplacian
import SupermodularGames.Multiplicity.TippingPoints
import SupermodularGames.Multiplicity.SShape
import SupermodularGames.Multiplicity.Bifurcation
-- import SupermodularGames.ComparativeStatics.Topkis
import SupermodularGames.Applications.BinaryAction
import SupermodularGames.Applications.MeanField
import SupermodularGames.Applications.GlobalGames
