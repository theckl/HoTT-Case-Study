import subset

universes u v w
hott_theory

namespace hott
open hott.set hott.subset 

namespace subset
variables {A : Set}

protected def inter (S₁ S₂ : Subset A) : Subset A :=
/- let P := λ a : A, a ∈ S₁ in -/
{a ∈ A | a ∈ S₁}

instance : has_inter (Subset A) :=
⟨subset.inter⟩

end subset

end hott