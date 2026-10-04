import C7Improvement.CertificateProfiles
import C7Improvement.Terminal
import ShannonBounds.CapC7
import ShannonBounds.Substitutions

namespace ShannonBounds.C7Improvement

open BaseC7
open Substitutions
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000

def productPowerIso {First Second Vertex : Type*} [Fintype First] [Fintype Second] [Fintype Vertex]
    [DecidableEq First] [DecidableEq Second] [DecidableEq Vertex]
    {firstGraph : SimpleGraph First} {secondGraph : SimpleGraph Second} {graph : SimpleGraph Vertex}
    [DecidableRel firstGraph.Adj] [DecidableRel secondGraph.Adj] [DecidableRel graph.Adj]
    {firstDimension secondDimension : ℕ}
    (firstIso : firstGraph ≃g SimpleGraph.strongPower graph firstDimension)
    (secondIso : secondGraph ≃g SimpleGraph.strongPower graph secondDimension) :
    strongProd firstGraph secondGraph ≃g SimpleGraph.strongPower graph (firstDimension + secondDimension) :=
  (strongProd_congr firstIso secondIso).trans
    (strongPower_add_iso graph firstDimension secondDimension).symm

def iso10 : strongProd G5 G5 ≃g SimpleGraph.strongPower Cyc7 10 :=
  productPowerIso CapC7.G5_iso CapC7.G5_iso

def iso15 : strongProd (strongProd G5 G5) G5 ≃g SimpleGraph.strongPower Cyc7 15 :=
  productPowerIso iso10 CapC7.G5_iso

def iso25 : strongProd (strongProd (strongProd G5 G5) G5) (strongProd G5 G5) ≃g
    SimpleGraph.strongPower Cyc7 25 := productPowerIso iso15 iso10

def iso30 : strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5) ≃g
    SimpleGraph.strongPower Cyc7 30 := productPowerIso iso15 iso15

def iso40 : strongProd
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
    (strongProd G5 G5) ≃g SimpleGraph.strongPower Cyc7 40 := productPowerIso iso30 iso10

def iso55 : strongProd
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd (strongProd G5 G5) G5))
    (strongProd (strongProd (strongProd G5 G5) G5) (strongProd G5 G5)) ≃g
    SimpleGraph.strongPower Cyc7 55 := productPowerIso iso30 iso25

attribute [local irreducible] G30n6 flipG55 new_G40

def R30 : Realisation Letter Letter.sep (SimpleGraph.strongPower Cyc7 30) :=
  G30n6.toRealisation.mapIso iso30

def R40 : Realisation Letter Letter.sep (SimpleGraph.strongPower Cyc7 40) :=
  new_G40.toRealisation.mapIso iso40

def R55 : Realisation Letter Letter.sep (SimpleGraph.strongPower Cyc7 55) :=
  flipG55.toRealisation.mapIso iso55

theorem R30_weights (letter : Letter) : R30.w letter = p30.weights letter := by
  rw [R30, Realisation.w_mapIso]
  exact hp30.weights letter

theorem R40_weights (letter : Letter) : R40.w letter = pNew40.weights letter := by
  rw [R40, Realisation.w_mapIso]
  exact hpNew40.weights letter

theorem R55_weights (letter : Letter) : R55.w letter = pFlip55.weights letter := by
  rw [R55, Realisation.w_mapIso]
  exact hpFlip55.weights letter

def simpleDimensions : Fin 3 → ℕ := ![30,55,55]
def strongDimensions : Fin 3 → ℕ := ![40,55,55]

def simpleChildren : (index : Fin 3) →
    Realisation Letter Letter.sep (SimpleGraph.strongPower Cyc7 (simpleDimensions index)) :=
  Fin.cases R30 (Fin.cases R55 (Fin.cases R55 (fun index => Fin.elim0 index)))

def strongChildren : (index : Fin 3) →
    Realisation Letter Letter.sep (SimpleGraph.strongPower Cyc7 (strongDimensions index)) :=
  Fin.cases R40 (Fin.cases R55 (Fin.cases R55 (fun index => Fin.elim0 index)))

def simpleInputWeights : Fin 3 → Letter → ℕ := ![p30.weights, pFlip55.weights, pFlip55.weights]
def strongInputWeights : Fin 3 → Letter → ℕ := ![pNew40.weights, pFlip55.weights, pFlip55.weights]

theorem simpleChildren_weights (index : Fin 3) (letter : Letter) :
    (simpleChildren index).w letter = simpleInputWeights index letter := by
  fin_cases index
  · exact R30_weights letter
  · exact R55_weights letter
  · exact R55_weights letter

theorem strongChildren_weights (index : Fin 3) (letter : Letter) :
    (strongChildren index).w letter = strongInputWeights index letter := by
  fin_cases index
  · exact R40_weights letter
  · exact R55_weights letter
  · exact R55_weights letter

def simpleRule := Realisation.multiSubst simpleDimensions simpleChildren S3b
def strongRule := Realisation.multiSubst strongDimensions strongChildren S3b

def simpleRuleWeights (letter : Letter) : ℕ :=
  ∑ word ∈ S3b.T letter, ∏ index : Fin 3, simpleInputWeights index (word index)

def strongRuleWeights (letter : Letter) : ℕ :=
  ∑ word ∈ S3b.T letter, ∏ index : Fin 3, strongInputWeights index (word index)

theorem simpleRule_weights (letter : Letter) : simpleRule.w letter = simpleRuleWeights letter := by
  rw [simpleRule, w_multiSubst]
  apply Finset.sum_congr rfl
  intro word memberWord
  apply Finset.prod_congr rfl
  intro index memberIndex
  exact simpleChildren_weights index (word index)

theorem strongRule_weights (letter : Letter) : strongRule.w letter = strongRuleWeights letter := by
  rw [strongRule, w_multiSubst]
  apply Finset.sum_congr rfl
  intro word memberWord
  apply Finset.prod_congr rfl
  intro index memberIndex
  exact strongChildren_weights index (word index)

end ShannonBounds.C7Improvement
