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

namespace subset
variables {A : Set.{u}}

@[hott]
protected def inter (S₁ S₂ : Subset A) : Subset A :=
{a ∈ A | a ∈ S₁ and a ∈ S₂ }

@[hott, instance]
def subset_inter : has_inter (Subset A) :=
⟨subset.inter⟩

@[hott]
def inter.symm (S₁ S₂ : Subset A) : S₁ ∩ S₂ = S₂ ∩ S₁ :=
  have ss1 : S₁ ∩ S₂ ⊆ S₂ ∩ S₁, from 
    assume a el, 
    have p : a ∈ S₁ and a ∈ S₂, from (pred_elem a).1 el,
    have q : a ∈ S₂ and a ∈ S₁, from ⟨p.2, p.1⟩,
    (pred_elem a).2 q,
  have ss2 : S₂ ∩ S₁ ⊆ S₁ ∩ S₂, from 
    assume a el, 
    have p : a ∈ S₂ and a ∈ S₁, from (pred_elem a).1 el,
    have q : a ∈ S₁ and a ∈ S₂, from ⟨p.2, p.1⟩,
    (pred_elem a).2 q,
  (sset_eq_iff_inclusion _ _).2 ⟨ss1, ss2⟩

@[hott]
def inter_sset_l (U V : Subset.{u} A) : U ∩ V ⊆ U :=
  assume a el, ((pred_elem a).1 el).1

@[hott]
def inter_sset_r (U V : Subset A) : U ∩ V ⊆ V :=
  by rwr inter.symm U V; exact inter_sset_l V U  

@[hott, reducible]
def sUnion (S : Subset (𝒫 A)) : Subset A := 
  {t ∈ A | prop_resize (∃ B ∈ S, t ∈ B)}

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

@[hott, reducible]
def iUnion {I : Set.{u}} (f : I -> 𝒫 A) : Subset A :=
  {t ∈ A | ∥ Σ i : I, t ∈ f i ∥}

hott_theory_cmd "local prefix `⋃ᵢ`:110 := hott.subset.iUnion"  

@[hott]
def sset_iUnion {I : Set.{u}} (f : I -> 𝒫 A) (i : I) : f i ⊆ ⋃ᵢ f :=
  assume a el, (pred_elem a).2 (@trunc.tr -1 (Σ i : I, a ∈ f i) ⟨i, el⟩) 
  
end subset

end hott