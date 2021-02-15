import subset set_axioms hott.types.prod

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open hott.set hott.subset prod

/- `⊆` induces a weak or partial order on the subsets of a set `A`:
   It is a reflexive, transitive and anti-symmetric relation. -/
@[hott, hsimp]
def subset_refl {A : Set.{u}} (B : Subset A) : B ⊆ B :=
  assume a a_in_B, a_in_B

@[hott, hsimp]
def subset_trans {A : Set.{u}} (B C D : Subset A) : 
  B ⊆ C -> C ⊆ D -> B ⊆ D :=
assume BC CD a a_in_B, CD a (BC a a_in_B)

@[hott, hsimp]
def subset_asymm {A : Set.{u}} (B C : Subset A) : 
  B ⊆ C -> C ⊆ B -> B = C :=
assume BC CB, (sset_eq_iff_inclusion B C).2 ⟨BC, CB⟩  

/- This should be in an [init]-file, maybe called [prop_logic]. It is not
   contained in [init.logic]. -/
@[hott]
protected def and (P Q : Prop) : Prop :=
  Prop.mk (P × Q) (prod.is_trunc_prod P Q -1)   

infix `and`:50 := hott.and 

namespace subset
variables {A : Set.{u}}

@[hott]
protected def inter (S₁ S₂ : Subset A) : Subset A :=
{a ∈ A | a ∈ S₁ and a ∈ S₂ }

@[hott, instance]
def subset_inter : has_inter (Subset A) :=
⟨subset.inter⟩

@[hott, reducible]
def sUnion (S : Subset (𝒫 A)) : Subset A := 
  {t ∈ A | prop_resize (∃ B ∈ S, t ∈ B)}

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

end subset

end hott