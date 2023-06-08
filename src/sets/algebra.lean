import sets.subset sets.axioms hott.types.prod 

universes u v w
hott_theory

namespace hott
open set subset prod trunc sum

set_option pp.universes true

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

@[hott, reducible]
protected def inter (S₁ S₂ : Subset A) : Subset A :=
  λ a : A, a ∈ S₁ and a ∈ S₂

@[hott, instance]
def subsets_have_inter : has_inter (Subset A) :=
  has_inter.mk (λ B C, hott.subset.inter B C) 

@[hott]
def elem_inter_iff (U V : Subset A) : 
  Π (a : A), a ∈ (U ∩ V) <-> (a ∈ U and a ∈ V) :=
begin
  intro a, apply pair,
  { intro el, exact (pred_elem a).1 el },
  { intro and_el, exact (pred_elem a).2 and_el }
end  

@[hott]
def elem_inter_eq (U V : Subset A) : 
  Π (a : A), a ∈ (U ∩ V) = (a ∈ U and a ∈ V) :=
λ a, prop_iff_eq (elem_inter_iff U V a).1 (elem_inter_iff U V a).2  

@[hott]
def inter.symm (S₁ S₂ : Subset A) : S₁ ∩ S₂ = S₂ ∩ S₁ :=
  have ss1 : (S₁ ∩ S₂) ⊆ (S₂ ∩ S₁), from 
    assume a el, 
    have p : a ∈ S₁ and a ∈ S₂, from (pred_elem a).1 el,
    have q : a ∈ S₂ and a ∈ S₁, from ⟨p.2, p.1⟩,
    (pred_elem a).2 q,
  have ss2 : (S₂ ∩ S₁) ⊆ (S₁ ∩ S₂), from 
    assume a el, 
    have p : a ∈ S₂ and a ∈ S₁, from (pred_elem a).1 el,
    have q : a ∈ S₁ and a ∈ S₂, from ⟨p.2, p.1⟩,
    (pred_elem a).2 q,
  (sset_eq_iff_inclusion _ _).2 ⟨ss1, ss2⟩

@[hott]
def inter_sset_l (U V : Subset A) : U ∩ V ⊆ U :=
  assume a el, 
  have p : a ∈ U and a ∈ V, from (pred_elem a).1 el,
  p.1

@[hott]
def inter_sset_r (U V : Subset A) : (U ∩ V) ⊆ V :=
  by rwr inter.symm U V; exact inter_sset_l V U  

@[hott, reducible]
def sInter (S : Subset (𝒫 A)) : Subset A := 
  λ t : A,  prop_resize.{u u+1} (to_Prop.{u+1} (∀ B : 𝒫 A, B ∈ S -> t ∈ B))

hott_theory_cmd "local prefix `⋂₀`:110 := hott.subset.sInter"

@[hott]
def sInter_sset {A : Set} (S : Subset (𝒫 A)) : 
  ∀ B : 𝒫 A, B ∈ S -> ⋂₀ S ⊆ B :=
assume B elB a ela, prop_resize_to_prop ((pred_elem a).1 ela) B elB 

@[hott]
def sset_sInter {A : Set} (S : Subset (𝒫 A)) (B : 𝒫 A) : 
  (∀ C : 𝒫 A, C ∈ S -> B ⊆ C) -> B ⊆ ⋂₀ S :=
begin  
  intros allBC a ela, apply (pred_elem a).2, apply prop_to_prop_resize,
  intros C elC, exact allBC C elC a ela
end    

@[hott, reducible]
def iInter {A : Set.{u}} {I : Set.{v}} (f : I -> Powerset A) : 
  Subset A :=
λ t : A, prop_resize.{u (max v u)} (to_Prop.{max v u} (∀ i : I, t ∈ f i))

@[hott, instance]
def sets_have_ind_inter (A : Set.{u}) (I : Set.{v}) : @has_ind_inter (Subset A) I :=
  has_ind_inter.mk (λ f, iInter f)  

@[hott]
def sset_iInter {A : Set} {I : Set} (f : I -> 𝒫 A) (i : I) : 
  (⋂ᵢ f) ⊆ (f i):=
begin intros a el, exact prop_resize_to_prop ((pred_elem a).1 el) i end  

@[hott, reducible]
protected def union (S₁ S₂ : Subset A) : Subset A :=
  λ a : A, a ∈ S₁ or a ∈ S₂

@[hott, instance]
def subsets_have_unions {A : Set} : has_union (Subset A) :=
  has_union.mk (λ S₁ S₂ : Subset A, subset.union S₁ S₂)

@[hott]
def union.symm (S₁ S₂ : Subset A) : S₁ ∪ S₂ = S₂ ∪ S₁ :=
  have ss1 : (S₁ ∪ S₂) ⊆ (S₂ ∪ S₁), from 
    assume a el, 
    have p : a ∈ S₁ or a ∈ S₂, from (pred_elem a).1 el,
    have q : a ∈ S₂ or a ∈ S₁, from or_symm p,
    (pred_elem a).2 q,
  have ss2 : (S₂ ∪ S₁) ⊆ (S₁ ∪ S₂), from 
    assume a el, 
    have p : a ∈ S₂ or a ∈ S₁, from (pred_elem a).1 el,
    have q : a ∈ S₁ or a ∈ S₂, from or_symm p,
    (pred_elem a).2 q,
  (sset_eq_iff_inclusion _ _).2 ⟨ss1, ss2⟩

@[hott]
def union_sset_l (U V : Subset A) : U ⊆ (U ∪ V) :=
begin intros a el, apply (pred_elem a).2, exact or_inl (a ∈ U) (a ∈ V) el end

@[hott]
def union_sset_r (U V : Subset A) : V ⊆ (U ∪ V) :=
  by rwr union.symm U V; exact union_sset_l V U 

@[hott, reducible]
def sUnion (S : Subset (𝒫 A)) : Subset A := 
  λ t : A, prop_resize.{u u+1} (@exists_elem (𝒫 A) (λ B : Subset A, S B and t ∈ B))

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

@[hott, reducible]
def iUnion {I : Set.{v}} (f : I -> Powerset A) : Subset A :=
  λ t : A, prop_resize.{u (max v u)} (∥ Σ i : I, t ∈ f i ∥)

@[hott, instance]
def sets_have_ind_union (I : Set.{v}) : @has_ind_union (Subset A) I :=
  has_ind_union.mk (λ f, iUnion f)

@[hott]
def sset_iUnion {A : Set} {I : Set} (f : I -> Powerset A) (i : I) : 
  (f i) ⊆ (⋃ᵢ f) :=
begin 
  intros a el, change ↥(prop_resize (∥ Σ i : I, a ∈ f i ∥)), 
  apply (pred_elem a).2, 
  exact prop_to_prop_resize (@trunc.tr -1 (Σ i : I, a ∈ f i) ⟨i, el⟩) 
end

@[hott]
def iUnion_sset {A : Set} {I : Set} (f : I -> 𝒫 A) (B : Subset A) :
  (∀ i : I, f i ⊆ B) -> ⋃ᵢ f ⊆ B :=
begin
  intros Iss a ela, let exi := prop_resize_to_prop ((pred_elem a).1 ela), 
  hinduction exi with elai,
  exact Iss elai.1 a elai.2
end    

@[hott]
protected def complement (U : Subset A) : Subset A :=
  λ x : A, x ∉ U

@[hott, instance]
def sets_have_compl (A : Set) : @has_complement (Subset A) :=
  has_complement.mk (λ U, subset.complement U)

@[hott]
def elem_comp_iff (U : Subset A) : Π a : A, a ∈ 𝒞(U) <-> a ∉ U :=
begin 
  intro a, apply pair, 
  { intro el, exact (@pred_elem A (λ a : A, a ∉ U) a).1 el },
  { intro not_el, exact (pred_elem a).2 not_el }
end    

@[hott]
def elem_comp_eq (U : Subset A) : Π a : A, a ∈ 𝒞(U) = a ∉ U :=
  λ a, prop_iff_eq (elem_comp_iff U a).1 (elem_comp_iff U a).2

@[hott]
def compl_total_empty : 𝒞(total_Subset A) = empty_Subset A :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a el, rwr elem_comp_eq _ a at el, 
    hinduction (el (all_elem a)) },
  { intros a el, hinduction empty_not_elem a el }
end   

@[hott]
def compl_inter (U V : Subset A) : 𝒞(U ∩ V) = 𝒞(U) ∪ 𝒞(V) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros x el,
    change ↥(x∈𝒞(U) or x∈𝒞(V)), 
    apply (pred_elem x).2, 
    have not_el_inter : ↥(x ∉ (U ∩ V)), from (pred_elem x).1 el,
    rwr elem_comp_eq, rwr elem_comp_eq, 
    apply (not_and (x∈U) (x∈V)).1, rwr <- elem_inter_eq, assumption },
  { intros x el, apply (elem_comp_iff (U ∩ V) x).2, 
    intro el', 
    have not_el_or : ↥(x∈𝒞(U) or x∈𝒞(V)), from (pred_elem x).1 el,
    rwr elem_comp_eq at not_el_or, rwr elem_comp_eq at not_el_or, 
    exact (not_and (x∈U) (x∈V)).2 not_el_or ((pred_elem x).1 el') }
end 

@[hott]
def compl_iUnion {I : Set} (f : I -> Powerset A) : 𝒞(⋃ᵢ f) = ⋂ᵢ (λ i, 𝒞(f i)) :=
begin  
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros x el, 
    apply (pred_elem x).2, apply prop_to_prop_resize,
    change Π (i : I), x∈𝒞(f i), intro i, apply (elem_comp_iff (f i) x).2, 
    intro el_i, apply (elem_comp_iff (⋃ᵢ f) x).1 el,
    apply (pred_elem x).2, exact prop_to_prop_resize (tr ⟨i, el_i⟩) },
  { intros x el, change ↥(x ∉ ⋃ᵢ f), intro el_Ui, 
    have i_el : Π i : I, x∈𝒞(f i), from prop_resize_to_prop ((pred_elem x).1 el),
    hinduction prop_resize_to_prop ((pred_elem x).1 el_Ui) with el_i, 
    exact (elem_comp_iff (f a.1) x).1 (i_el a.1) a.2 }
end  

@[hott]
def setminus (U V : Subset A) : Subset A :=
  λ x : A, (x ∈ U) and (x ∉ V)

/- Lists of elements of a set define subsets. -/
@[hott]
def elem_to_Subset {S : Set} (a : S) : Subset S :=
  λ b, to_Prop (b = a)

@[hott]
def list_to_Subset {S : Set} (l : list S) : Subset S :=
begin hinduction l with hd tl S', exact empty_Subset S, exact S' ∪ (elem_to_Subset hd) end

end subset

end hott