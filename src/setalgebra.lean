import subset set_axioms hott.types.prod 

universes u v w
hott_theory

namespace hott
open hott.set hott.subset prod trunc sum

/- `⊆` induces a weak or partial order on the subsets of a set `A`:
   It is a reflexive, transitive and anti-symmetric relation. -/
@[hott, hsimp]
def subset_refl {A : Set} (B : Subset A) : B ⊆ B :=
  assume a a_in_B, a_in_B

@[hott, hsimp]
def subset_trans {A : Set} (B C D : Subset A) : 
  B ⊆ C -> C ⊆ D -> B ⊆ D :=
assume BC CD a a_in_B, CD a (BC a a_in_B)

@[hott, hsimp]
def subset_asymm {A : Set} (B C : Subset A) : 
  B ⊆ C -> C ⊆ B -> B = C :=
assume BC CB, (sset_eq_iff_inclusion B C).2 ⟨BC, CB⟩  

namespace subset
variables {A : Set}

@[hott, reducible]
protected def inter (S₁ S₂ : Subset A) : Subset A :=
{a ∈ A | a ∈ S₁ and a ∈ S₂}

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
def inter_sset_l (U V : Subset A) : (subset.inter U V) ⊆ U :=
  assume a el, 
  have p : a ∈ U and a ∈ V, from (pred_elem a).1 el,
  p.1

@[hott]
def inter_sset_r (U V : Subset A) : is_Subset_of (U ∩ V) V :=
  by rwr inter.symm U V; exact inter_sset_l V U  

@[hott, reducible]
def sInter (S : Subset (𝒫 A)) : Subset A := 
  {t ∈ A | prop_resize (to_Prop (∀ B : 𝒫 A, B ∈ S -> t ∈ B))}

hott_theory_cmd "local prefix `⋂₀`:110 := hott.subset.sInter"

@[hott, reducible]
def iInter {A : Set.{u}} {I : Set.{u}} (f : I -> 𝒫 A) : Subset A :=
  {t ∈ A | to_Prop (∀ i : I, t ∈ f i) }

hott_theory_cmd "local prefix `⋂ᵢ`:110 := hott.subset.iInter"  

@[hott]
def sset_iInter {A : Set.{u}} {I : Set.{u}} (f : I -> 𝒫 A) (i : I) : 
  (⋂ᵢ f) ⊆ (f i):=
begin intros a el, exact (pred_elem a).1 el i end  

@[hott, reducible]
protected def union (S₁ S₂ : Subset A) : Subset A :=
{a ∈ A | a ∈ S₁ or a ∈ S₂}

@[hott, instance]
def subset_union : has_union (Subset A) :=
⟨subset.union⟩

@[hott]
def union.symm (S₁ S₂ : Subset A) : S₁ ∪ S₂ = S₂ ∪ S₁ :=
  have ss1 : S₁ ∪ S₂ ⊆ S₂ ∪ S₁, from 
    assume a el, 
    have p : a ∈ S₁ or a ∈ S₂, from (pred_elem a).1 el,
    have q : a ∈ S₂ or a ∈ S₁, from or_symm p,
    (pred_elem a).2 q,
  have ss2 : S₂ ∪ S₁ ⊆ S₁ ∪ S₂, from 
    assume a el, 
    have p : a ∈ S₂ or a ∈ S₁, from (pred_elem a).1 el,
    have q : a ∈ S₁ or a ∈ S₂, from or_symm p,
    (pred_elem a).2 q,
  (sset_eq_iff_inclusion _ _).2 ⟨ss1, ss2⟩

@[hott]
def union_sset_l (U V : Subset A) : U ⊆ U ∪ V:=
begin intros a el, apply (pred_elem a).2, exact or_inl (a ∈ U) (a ∈ V) el end

@[hott]
def union_sset_r (U V : Subset A) : V ⊆ U ∪ V :=
  by rwr union.symm U V; exact union_sset_l V U 

@[hott, reducible]
def sUnion (S : Subset (𝒫 A)) : Subset A := 
  {t ∈ A | prop_resize (∃ B ∈ S, t ∈ B)}

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

@[hott, reducible]
def iUnion {A : Set.{u}} {I : Set.{u}} (f : I -> 𝒫 A) : Subset A :=
  {t ∈ A | ∥ Σ i : I, t ∈ f i ∥}

hott_theory_cmd "local prefix `⋃ᵢ`:110 := hott.subset.iUnion"  

@[hott]
def sset_iUnion {A : Set.{u}} {I : Set.{u}} (f : I -> 𝒫 A) (i : I) : 
  (f i) ⊆ (⋃ᵢ f) :=
assume a el, (pred_elem a).2 (@trunc.tr -1 (Σ i : I, a ∈ f i) ⟨i, el⟩) 

@[hott]
def complement (U : Subset A) : Subset A :=
  {x ∈ A | x ∉ U}

notation `C(`U`)` := complement U  

@[hott]
def compl_total_empty : C(total_Subset A) = empty_Subset A :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a el, 
    have not_el : ↥(a ∉ (total_Subset A)), from (pred_elem a).1 el,
    have el' : ↥(a ∈ (total_Subset A)), from all_elem a,
    hinduction (not_el el') },
  { intros a el, apply (pred_elem a).2, intro ne_all, 
    exact empty_not_elem a el }
end   

end subset

end hott