import subset hott.types.prod

universes u v w
hott_theory

namespace hott
open hott.set hott.subset prod

/- This should be in an [init]-file, maybe called [prop_logic]. It is not
   contained in [init.logic]. -/
@[hott]
protected def and (P Q : Prop) : Prop :=
  Prop.mk (P × Q) (prod.is_trunc_prod P Q -1)   

infix `and`:50 := hott.and 

namespace subset
variables {A : Set}

@[hott]
protected def inter (S₁ S₂ : Subset A) : Subset A :=
{a ∈ A | a ∈ S₁ and a ∈ S₂ }

@[hott]
instance : has_inter (Subset A) :=
⟨subset.inter⟩

@[hott, reducible]
def sUnion (S : Subset (𝒫 A)) : Subset A := {t ∈ A | ∃ B ∈ S, t ∈ B}

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

end subset

end hott