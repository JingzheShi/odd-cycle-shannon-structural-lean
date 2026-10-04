import C7Improvement.CountC1

namespace ShannonBounds.C7Improvement

open BaseC7 RichPortSystem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

attribute [local irreducible] G10 G10A G10D BaseC7.base Jplus

def G15X : RichPortSystem (strongProd (strongProd G5 G5) G5) := gao G10 BaseC7.base

def G15AX : RichPortSystem (strongProd (strongProd G5 G5) G5) := gao G10A BaseC7.base

def G15DX : RichPortSystem (strongProd (strongProd G5 G5) G5) := gao G10D (flip BaseC7.base)

def G15het : RichPortSystem (strongProd (strongProd G5 G5) G5) :=
  heterogeneousGao G10 BaseC7.base G10.X Jplus Jplus
    G10.hX Jplus_independent Jplus_independent G10.hsep

theorem G15het_sibling : G15het.I = G15X.I ∧ G15het.ports = G15X.ports ∧
    G15het.ep = G15X.ep ∧ G15het.side = G15X.side := ⟨rfl, rfl, rfl, rfl⟩

end ShannonBounds.C7Improvement
