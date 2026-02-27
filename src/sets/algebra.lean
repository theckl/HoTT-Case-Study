import sets.subset

universes u v w
hott_theory

namespace hott
open hott.set subset prod trunc is_trunc sum

--set_option pp.universes true

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

@[hott]
def empty_sset {A : Set.{u}} (B : Subset A) : empty_Subset A ⊆ B :=
  begin intros a inc, hinduction inc end

namespace subset

@[hott, reducible]
protected def inter {A : Set.{u}} (S₁ S₂ : Subset A) : Subset A :=
  λ a : A, a ∈ S₁ and a ∈ S₂

@[hott, instance]
def subsets_have_inter {A : Set.{u}} : has_inter (Subset A) :=
  has_inter.mk (λ B C, hott.subset.inter B C) 

@[hott]
def elem_inter_iff {A : Set.{u}} (U V : Subset A) : 
  Π (a : A), a ∈ (U ∩ V) <-> (a ∈ U and a ∈ V) :=
begin
  intro a, apply pair,
  { intro el, exact (pred_elem a).1 el },
  { intro and_el, exact (pred_elem a).2 and_el }
end  

@[hott]
def inc_inc_inter_inc {A : Set.{u}} {S₁ S₂ T : Subset A} : 
  T ⊆ S₁ -> T ⊆ S₂ -> T ⊆ (S₁ ∩ S₂) := 
begin 
  intros inc₁ inc₂ a inc_T, 
  exact (elem_inter_iff S₁ S₂ a).2 (inc₁ a inc_T, inc₂ a inc_T) 
end

@[hott]
def elem_inter_eq {A : Set.{u}} (U V : Subset A) : 
  Π (a : A), a ∈ (U ∩ V) = (a ∈ U and a ∈ V) :=
λ a, prop_iff_eq (elem_inter_iff U V a).1 (elem_inter_iff U V a).2  

@[hott]
def inter.symm {A : Set.{u}} (S₁ S₂ : Subset A) : S₁ ∩ S₂ = S₂ ∩ S₁ :=
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
def inter_sset_l {A : Set.{u}} (U V : Subset A) : U ∩ V ⊆ U :=
  assume a el, 
  have p : a ∈ U and a ∈ V, from (pred_elem a).1 el,
  p.1

@[hott]
def inter_sset_r {A : Set.{u}} (U V : Subset A) : (U ∩ V) ⊆ V :=
  by rwr inter.symm U V; exact inter_sset_l V U  

@[hott, reducible]
def sInter {A : Set.{u}} (S : Subset (𝒫 A)) : Subset A := 
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
protected def union {A : Set.{u}} (S₁ S₂ : Subset A) : Subset A :=
  λ a : A, a ∈ S₁ or a ∈ S₂

@[hott, instance]
def subsets_have_unions {A : Set} : has_union (Subset A) :=
  has_union.mk (λ S₁ S₂ : Subset A, subset.union S₁ S₂)

@[hott]
def union.symm {A : Set.{u}} (S₁ S₂ : Subset A) : S₁ ∪ S₂ = S₂ ∪ S₁ :=
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
def union_sset_l {A : Set.{u}} (U V : Subset A) : U ⊆ (U ∪ V) :=
begin intros a el, apply (pred_elem a).2, exact or_inl (a ∈ U) (a ∈ V) el end

@[hott]
def union_sset_r {A : Set.{u}} (U V : Subset A) : V ⊆ (U ∪ V) :=
  by rwr union.symm U V; exact union_sset_l V U 

@[hott]
def elem_union_iff {A : Set.{u}} (U V : Subset A) : 
  Π (a : A), a ∈ (U ∪ V) <-> (a ∈ U or a ∈ V) :=
begin
  intro a, apply pair,
  { intro el, exact (pred_elem a).1 el },
  { intro or_el, exact (pred_elem a).2 or_el }
end 

@[hott]
def inc_inc_union_inc {A : Set.{u}} {S₁ S₂ T : Subset A} : 
  S₁ ⊆ T -> S₂ ⊆ T -> (S₁ ∪ S₂) ⊆ T := 
begin 
  intros inc₁ inc₂ a inc_S, hinduction inc_S with sum_S, 
  hinduction sum_S with inc_S₁ inc_S₂, 
  exact inc₁ a inc_S₁, exact inc₂ a inc_S₂, 
end

@[hott]
def union.idempot {A : Set.{u}} {S : Subset A} : S ∪ S = S :=
begin
  fapply (sset_eq_iff_inclusion _ _).2, fapply pair,
    fapply inc_inc_union_inc, exact subset_refl S, exact subset_refl S,
    exact union_sset_l S S
end

@[hott]
def empty_union {A : Set.{u}} (S : Subset A) : empty_Subset A ∪ S = S :=
begin 
  fapply (sset_eq_iff_inclusion _ _).2, fapply pair,
  { apply inc_inc_union_inc, exact empty_sset _, exact subset_refl _ },
  { exact union_sset_r _ _ } 
end

@[hott, reducible]
def sUnion {A : Set.{u}} (S : Subset (𝒫 A)) : Subset A := 
  λ t : A, prop_resize.{u u+1} (@exists_elem (𝒫 A) (λ B : Subset A, S B and t ∈ B))

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

@[hott, reducible]
def iUnion {A : Set.{u}} {I : Set.{v}} (f : I -> Powerset A) : Subset A :=
  λ t : A, prop_resize.{u (max v u)} (∥ Σ i : I, t ∈ f i ∥)

hott_theory_cmd "local prefix `⋃ᵢ`:110 := hott.subset.iUnion"

@[hott]
def empty_iUnion_empty {A : Set.{u}} (f : empty_Set -> Powerset A) : 
  ⋃ᵢ f = empty_Subset A :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a el, hinduction prop_resize_to_prop el, hinduction a_1.1 },
  { intros a el, hinduction el }
end

@[hott]
def iUnion_index_bij {A : Set.{u}} {I J : Set.{v}} (f : I -> Powerset A) 
  (h : bijection J I) : ⋃ᵢ f = ⋃ᵢ (f ∘ h) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a el, apply prop_to_prop_resize, hinduction prop_resize_to_prop el, 
    apply tr, fapply sigma.mk, exact (inv_bijection_of h) a_1.1, 
    change ↥(a ∈ f (h.map ((inv_bijection_of h).map a_1.1))), rwr inv_bij_r_inv, exact a_1.2 },
  { intros a el, apply prop_to_prop_resize, hinduction prop_resize_to_prop el, 
    apply tr, fapply sigma.mk, exact h a_1.1, exact a_1.2 }
end

@[hott, instance]
def sets_have_ind_union {A : Set.{u}} {I : Set.{v}} (f : I -> Subset A) : 
  @has_ind_union (Subset A) I f :=
has_ind_union.mk f (iUnion f)

@[hott]
def sset_iUnion {A : Set.{u}} {I : Set.{v}} (f : I -> Powerset A) (i : I) : 
  (f i) ⊆ (⋃ᵢ f) :=
begin 
  intros a el, change ↥(prop_resize.{u (max v u)} (∥ Σ i : I, a ∈ f i ∥)), 
  apply (pred_elem a).2, 
  exact prop_to_prop_resize (@trunc.tr -1 (Σ i : I, a ∈ f i) ⟨i, el⟩) 
end

@[hott]
def iUnion_sset {A : Set.{u}} {I : Set.{v}} (f : I -> 𝒫 A) (B : Subset A) :
  (∀ i : I, f i ⊆ B) -> ⋃ᵢ f ⊆ B :=
begin
  intros Iss a ela, let exi := prop_resize_to_prop ((pred_elem a).1 ela), 
  hinduction exi with elai,
  exact Iss elai.1 a elai.2
end  

@[hott]
def sset_comp_iUnion {A : Set.{u}} {I : Set.{v}} (f : I -> 𝒫 A) (B : Subset A) :
  (Σ i : I, B ⊆ f i) -> B ⊆ ⋃ᵢ f :=
begin intro inc_i_f, exact subset_trans _ _ _ inc_i_f.2 (sset_iUnion f inc_i_f.1) end

@[hott]
protected def complement {A : Set.{u}} (U : Subset A) : Subset A :=
  λ x : A, x ∉ U

@[hott, instance]
def sets_have_compl (A : Set) : @has_complement (Subset A) :=
  has_complement.mk (λ U, subset.complement U)

@[hott]
def elem_comp_iff {A : Set.{u}} (U : Subset A) : Π a : A, a ∈ 𝒞(U) <-> a ∉ U :=
begin 
  intro a, apply pair, 
  { intro el, exact (@pred_elem A (λ a : A, a ∉ U) a).1 el },
  { intro not_el, exact (pred_elem a).2 not_el }
end    

@[hott]
def elem_comp_eq {A : Set.{u}} (U : Subset A) : Π a : A, a ∈ 𝒞(U) = a ∉ U :=
  λ a, prop_iff_eq (elem_comp_iff U a).1 (elem_comp_iff U a).2

@[hott]
def compl_total_empty {A : Set.{u}} : 𝒞(total_Subset A) = empty_Subset A :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a el, rwr elem_comp_eq _ a at el, 
    hinduction (el (all_elem a)) },
  { intros a el, hinduction empty_not_elem a el }
end   

@[hott]
def compl_inter {A : Set.{u}} (U V : Subset A) : 𝒞(U ∩ V) = 𝒞(U) ∪ 𝒞(V) :=
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

/- Complements of subsets only satisfy "boolean" properties if LEM holds (at least for
   the element relation in the surrounding set). -/
@[hott]
def compl_union_top {A : Set.{u}} (U : Subset A) [H : has_dec_elem A] : U ∪ 𝒞(U) = total_Subset A :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, exact true.intro },
  { intros a inc, let a_na := @has_dec_elem.dec_el A H a U, hinduction a_na with ae nae, 
    exact or_inl _ _ ae, exact or_inr _ _ nae }
end

@[hott]
def compl_inter_bottom {A : Set.{u}} (U : Subset A) : U ∩ 𝒞(U) = empty_Subset A :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, hinduction inc.2 inc.1 },
  { intros a inc, hinduction inc }
end     

@[hott]
def compl_iUnion {A : Set.{u}} {I : Set} (f : I -> Powerset A) : 𝒞(⋃ᵢ f) = ⋂ᵢ (λ i, 𝒞(f i)) :=
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
def setminus {A : Set.{u}} (U V : Subset A) : Subset A :=
  λ x : A, (x ∈ U) and (x ∉ V)

@[hott]
def set_minus_inc {A : Set.{u}} (U V : Subset A) : setminus U V ⊆ U :=
begin intros x inc, exact inc.1 end

@[hott]
def set_minus_inc_impl {A : Set.{u}} (U V W : Subset A) [H : has_dec_elem A] : 
  setminus U V ⊆ W -> U ⊆ (W ∪ V) :=
begin 
  intros sm_inc x inc, hinduction (has_dec_elem.dec_el x V), 
  exact union_sset_r _ _ x val, exact union_sset_l _ _ x (sm_inc x (inc, val)) 
end

@[hott]
def setminus_disjoint  {A : Set.{u}} (U V : Subset A) : 
  V ∩ (setminus U V) = empty_Subset A :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, fapply prod.mk, 
    intros a inc, hinduction inc.2.2 inc.1,
    intros a inc, hinduction inc 
end

@[hott]
def inc_setminus_inc {A : Set.{u}} (U V W : Subset A) : 
  U ⊆ V -> setminus U W ⊆ setminus V W :=
begin intros ss a inc, fapply prod.mk, exact ss a inc.1, exact inc.2 end 

/- Lists of elements of a set define subsets. -/

/-@[hott]
def list_to_Subset {S : Set} (l : list S) : Subset S :=
begin hinduction l with hd tl S', exact empty_Subset S, exact S' ∪ (singleton_sset hd) end
-/
end subset

end hott