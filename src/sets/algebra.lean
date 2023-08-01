import sets.subset sets.finite sets.axioms hott.types.prod 

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

@[hott, reducible]
def sUnion {A : Set.{u}} (S : Subset (𝒫 A)) : Subset A := 
  λ t : A, prop_resize.{u u+1} (@exists_elem (𝒫 A) (λ B : Subset A, S B and t ∈ B))

hott_theory_cmd "local prefix `⋃₀`:110 := hott.subset.sUnion"

@[hott, reducible]
def iUnion {A : Set.{u}} {I : Set.{v}} (f : I -> Powerset A) : Subset A :=
  λ t : A, prop_resize.{u (max v u)} (∥ Σ i : I, t ∈ f i ∥)

@[hott, instance]
def sets_have_ind_union {A : Set.{u}} (I : Set.{v}) : @has_ind_union (Subset A) I :=
  has_ind_union.mk (λ f, iUnion f)

@[hott]
def sset_iUnion {A : Set.{u}} {I : Set.{v}} (f : I -> Powerset A) (i : I) : 
  (f i) ⊆ (⋃ᵢ f) :=
begin 
  intros a el, change ↥(prop_resize.{u (max v u)} (∥ Σ i : I, a ∈ f i ∥)), 
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

/- Lists of elements of a set define subsets. -/
@[hott]
def list_to_Subset {S : Set} (l : list S) : Subset S :=
begin hinduction l with hd tl S', exact empty_Subset S, exact S' ∪ (singleton_sset hd) end

/- When dealing with variables of a first-order language we need inclusion of decidable 
   subsets and their properties, and that intersections, unions and complements of 
   decidable subsets are again decidable. -/
@[hott]
def dec_inc_to_inc {S : Set} {A B : dec_Subset S} : 
  A ⊆ B -> dec_sset_to_sset A ⊆ dec_sset_to_sset B :=
begin intros dec_inc x el_A, exact dec_inc x el_A end

@[hott]
def inc_to_dec_inc {S : Set} {A B : dec_Subset S} : 
  dec_sset_to_sset A ⊆ dec_sset_to_sset B -> A ⊆ B :=
begin intros inc x el_A, exact inc x el_A end 

@[hott, reducible]
protected def dec_inter {A : Set.{u}} (S₁ S₂ : dec_Subset A) : dec_Subset A :=
λ a : A, @Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) 
                                 (λ t, Two.rec Two.zero Two.zero t) 
                                 (λ t, Two.rec Two.zero Two.one t) (S₁ a) (S₂ a)

@[hott, instance]
def dec_subsets_have_dec_inter {A : Set.{u}} : has_inter (dec_Subset A) :=
  has_inter.mk (λ B C, hott.subset.dec_inter B C)

@[hott]
def dec_inter_is_inter {A : Set.{u}} (S₁ S₂ : dec_Subset A) : 
  dec_sset_to_sset (S₁ ∩ S₂) = dec_sset_to_sset S₁ ∩ dec_sset_to_sset S₂ :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } },
    apply pair, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro, 
                change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₂, exact true.intro },
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    change ↥((@Two.rec (λ t : Two, Prop) _ _ _) and (@Two.rec (λ t : Two, Prop) _ _ _)) 
           at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { rwr t₁ at inc, rwr t₂ at inc, hinduction inc },
    all_goals { try {hinduction fst } }, all_goals { try {hinduction snd } },
    exact true.intro }
end 

@[hott, reducible]
protected def dec_union {A : Set.{u}} (S₁ S₂ : dec_Subset A) : dec_Subset A :=
λ a : A, @Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) 
                                 (λ t, Two.rec Two.zero Two.one t) 
                                 (λ t, Two.rec Two.one Two.one t) (S₁ a) (S₂ a)

@[hott, instance]
def dec_subsets_have_dec_union {A : Set.{u}} : has_union (dec_Subset A) :=
  has_union.mk (λ B C, hott.subset.dec_union B C)

@[hott]
def dec_union_is_union {A : Set.{u}} (S₁ S₂ : dec_Subset A) : 
  dec_sset_to_sset (S₁ ∪ S₂) = dec_sset_to_sset S₁ ∪ dec_sset_to_sset S₂ :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } },
    all_goals { change ↥(∥ _ ∥), apply tr },  
    apply sum.inr, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₂, exact true.intro, 
    apply sum.inl, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro,
    apply sum.inl, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro },
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    change ↥((@Two.rec (λ t : Two, Prop) _ _ _) or (@Two.rec (λ t : Two, Prop) _ _ _)) 
           at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { rwr t₁ at inc, rwr t₂ at inc, hinduction inc with sum, hinduction sum },
    all_goals { try {hinduction val } }, 
    all_goals { try { exact true.intro } } }
end

/- Without further assumptions we can only show that finite intersections and unions of 
   decidable subsets are decidable subsets. -/
@[hott, reducible]
def dec_fin_iInter {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  dec_Subset A :=
begin 
  hinduction n, exact λ a : A, Two.one, 
  exact subset.dec_inter (ih (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) 
                         (f ⟨n, nat.le_refl (n+1)⟩)
end

@[hott, instance]
def dec_ssets_have_ind_inter (A : Set.{u}) {n : ℕ} : 
  @has_ind_inter (dec_Subset A) (fin_Set n) :=
has_ind_inter.mk (λ f, @dec_fin_iInter A n f)  

@[hott]
def dec_fin_iInter_is_iInter {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  dec_sset_to_sset (⋂ᵢ f) = ⋂ᵢ (λ m : fin_Set n, dec_sset_to_sset (f m)) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, apply prop_to_prop_resize, hinduction n, 
      intro m, hinduction nat.not_lt_zero m.1 m.2,
      have p : (⋂ᵢ f) = (⋂ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∩ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
      rwr p at inc, rwr dec_inter_is_inter at inc, 
      intro m, hinduction m with m q, change ↥(dec_sset_to_sset (f ⟨m, q⟩) a),
      hinduction nat.eq_sum_lt_of_le q, 
        have q : sigma.mk m q = ⟨n, nat.le_refl (n + 1)⟩, from
        begin 
          fapply sigma.sigma_eq, exact (nat.succ.inj val), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end, 
        rwr q, exact inc.2, 
        have q' : m < n, from nat.lt_of_succ_lt_succ val,
        let f' := λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩,
        have r : f ⟨m, q⟩ = f' ⟨m, q'⟩, from 
        begin 
          change _ = f ⟨m, nat.le.step q'⟩, apply ap f, fapply sigma.sigma_eq,
          refl, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end,
        rwr r, exact ih f' inc.1 ⟨m, q'⟩ },
  { intros a inc, hinduction n,
    exact true.intro,
    have p : (⋂ᵢ f) = (⋂ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∩ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
    rwr p, rwr dec_inter_is_inter, apply pair,
    apply ih (λ (m : ↥(fin_Set n)), f ⟨m.fst, nat.le.step m.snd⟩), 
    apply prop_to_prop_resize, intro m,  
    exact prop_resize_to_prop inc ⟨m.fst, nat.le.step m.snd⟩,
    exact prop_resize_to_prop inc ⟨n, nat.le_refl (n+1)⟩ }
end

@[hott, reducible]
def dec_fin_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  dec_Subset A :=
begin 
  hinduction n, exact λ a : A, Two.zero, 
  exact subset.dec_union (ih (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) 
                         (f ⟨n, nat.le_refl (n+1)⟩)
end

@[hott, instance]
def dec_ssets_have_ind_union (A : Set.{u}) {n : ℕ} : 
  @has_ind_union (dec_Subset A) (fin_Set n) :=
has_ind_union.mk (λ f, @dec_fin_iUnion A n f)

@[hott]
def dec_fin_iUnion_is_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  dec_sset_to_sset (⋃ᵢ f) = ⋃ᵢ (λ m : fin_Set n, dec_sset_to_sset (f m)) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, apply prop_to_prop_resize, hinduction n, 
    hinduction inc,
    have p : (⋃ᵢ f) = (⋃ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∪ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
    rwr p at inc, rwr dec_union_is_union at inc,
    hinduction inc with inc, hinduction inc with inc₁ inc₂,
      hinduction ih _ inc₁ with eq₁ i_inc₁, apply tr, fapply sigma.mk, 
        exact ⟨i_inc₁.1.1, nat.le.step i_inc₁.1.2⟩, exact i_inc₁.2,
      apply tr, exact ⟨⟨n, nat.le_refl (n + 1)⟩, inc₂⟩ },
  { intros a inc, hinduction n,
      hinduction prop_resize_to_prop inc with eq i_inc, -- n=0
      hinduction nat.not_lt_zero i_inc.1.1 i_inc.1.2,      
      hinduction prop_resize_to_prop inc with eq i_inc, clear eq, -- n -> n+1
      have p : (⋃ᵢ f) = (⋃ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∪ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
      rwr p, rwr dec_union_is_union, apply tr, 
      hinduction nat.eq_sum_lt_of_le i_inc.1.2,
        apply sum.inr,                                        -- m = n
        have q : i_inc.1 = ⟨n, nat.le_refl (n + 1)⟩, from
        begin 
          fapply sigma.sigma_eq, exact (nat.succ.inj val), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end, 
        rwr <- q, exact i_inc.2,
        apply sum.inl, apply ih (λ m, f ⟨m.fst, nat.le.step m.snd⟩),    -- m < n 
        apply prop_to_prop_resize, apply tr, fapply sigma.mk,
        have r : i_inc.1.1 < n, from nat.lt_of_succ_lt_succ val, 
        exact ⟨i_inc.1.1, r⟩, 
        change ↥(a∈dec_sset_to_sset (f _)), hsimp,
        have r' : i_inc.1 = ⟨i_inc.fst.fst, nat.le.step (nat.lt_of_succ_lt_succ val)⟩, from
        begin 
          hinduction i_inc.1, fapply sigma.sigma_eq, refl, 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end,
        rwr <- r', exact i_inc.2 }
end

/- The complement of a decidable subset is decidable. -/
@[hott]
protected def dec_complement {A : Set.{u}} (U : dec_Subset A) : dec_Subset A :=
  λ x : A, @Two.rec (λ t : Two, Two) Two.one Two.zero (U x) 

@[hott, instance]
def dec_sets_have_compl (A : Set) : @has_complement (dec_Subset A) :=
  has_complement.mk (λ U, subset.dec_complement U)

@[hott]
def dec_compl_is_compl {A : Set} (U : dec_Subset A) : 
  dec_sset_to_sset (𝒞 U) = 𝒞 (dec_sset_to_sset U) :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, hinduction U a with t,
    intro inc', change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc', -- U a = zero
    rwr t at inc', hinduction inc',
    have p : (𝒞 U) a = Two.zero, from           -- U a = one
        begin change (@Two.rec (λ t : Two, Two) _ _ _) = _, rwr t end,  
    change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc, rwr p at inc, hinduction inc },
  { intros a inc, hinduction U a with t, 
      have p : (𝒞 U) a = Two.one, from           -- U a = zero
        begin change (@Two.rec (λ t : Two, Two) _ _ _) = _, rwr t end, 
      change ↥(@Two.rec (λ t : Two, Prop) _ _ ((𝒞 U) a)), rwr p, exact true.intro, 
      have inc' : ↥(a ∈ dec_sset_to_sset U), from -- U a = one
        begin change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t, exact true.intro end,  
      hinduction inc inc' } 
end

/- The set-minus of two decidable subsets is decidable. -/
@[hott]
def dec_setminus {A : Set.{u}} (U V : dec_Subset A) : dec_Subset A :=
  λ a : A, @Two.rec (λ t : Two, Two -> Two) 
                       (λ t', @Two.rec (λ t', Two) Two.zero Two.zero (V a))
                       (λ t', @Two.rec (λ t', Two) Two.one Two.zero (V a)) (U a) (V a)

@[hott]
def dec_setminus_is_setminus {A : Set.{u}} (U V : dec_Subset A) :
  dec_sset_to_sset (dec_setminus U V) = 
                                 setminus (dec_sset_to_sset U) (dec_sset_to_sset V) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction U a with t₁, all_goals { hinduction V a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } }, apply pair, 
    change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro, 
    intro inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc, rwr t₂ at inc, 
    hinduction inc },
  { intros a inc, 
    change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    hinduction inc with inc₁ inc₂,
    hinduction U a with t₁, all_goals { hinduction V a with t₂ }, 
    all_goals { try { change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc₁, 
                      rwr t₁ at inc₁, hinduction inc₁ } },
    all_goals { hsimp }, exact true.intro, 
    change ↥(Not (@Two.rec (λ t : Two, Prop) _ _ _)) at inc₂, rwr t₂ at inc₂, 
    hinduction inc₂ true.intro }
end

/- Without additional assumptions, infinite intersections and unions of decidable subsets
   in a set `A` cannot be constructed as decidable subsets of `A`. One possibility is to 
   assume that `A` has decidable equality and that the underlying sets of intersection 
   and union are finite: Then intersection and union are decidable, since all finite 
   subsets of `A` are decidable, see [sets.finite]. -/

end subset

end hott