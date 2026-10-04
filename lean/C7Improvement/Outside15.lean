import C7Improvement.G15

namespace ShannonBounds.C7Improvement

open BaseC7

attribute [local irreducible] G15X

def outside15 (point : (BaseC7.Code × BaseC7.Code) × BaseC7.Code) : Prop :=
  ¬ near (strongProd (strongProd G5 G5) G5) G15X.Xstar point

instance : DecidablePred outside15 := fun point =>
  inferInstanceAs (Decidable (¬ near (strongProd (strongProd G5 G5) G5) G15X.Xstar point))

end ShannonBounds.C7Improvement
