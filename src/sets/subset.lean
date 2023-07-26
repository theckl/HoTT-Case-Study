import prop_logic sets.basic 

universes u v w
hott_theory

namespace hott
open hott.set hott.is_trunc hott.is_equiv hott.eq hott.trunc hott.sigma 

/- We define classes and notations that can be used to introduce `∈`, `⊆`, arbitrary 
   intersections `⋂ᵢ` and unions `⋃ᵢ` indexed by sets and complements `𝒞` for 
   (sub)sets, but also for other types. -/
@[hott]
class has_mem {A B : Type _} := (is_mem : A -> B -> trunctype -1)

hott_theory_cmd "local infix `∈`:70 := hott.has_mem.is_mem"
hott_theory_cmd "local infix  `∉`:70 := λ a b, hott.Not (hott.has_mem.is_mem a b)"  

@[hott]
class has_subset {A : Type _} := (is_subset : A -> A -> trunctype -1)

hott_theory_cmd "local infix `⊆`:70 := hott.has_subset.is_subset"

@[hott]
class has_ind_inter {A : Type _} {I : Set} := (ind_inter : (I -> A) -> A) 

hott_theory_cmd "local prefix `⋂ᵢ`:110 := hott.has_ind_inter.ind_inter"

@[hott]
class has_ind_union {A : Type _} {I : Set} := (ind_union : (I -> A) -> A) 

hott_theory_cmd "local prefix `⋃ᵢ`:110 := hott.has_ind_union.ind_union"

@[hott]
class has_complement {A : Type _} := (compl : A -> A)

hott_theory_cmd "local prefix `𝒞`:110 := hott.has_complement.compl"


namespace subset

--set_option pp.universes true

/- We define subsets of sets [A] by predicates on `A`, with a 
   coercion to the set of all elements of `A` satisfying the predicate, 
   and a coercion of the objects of this set to the elements of `A`. 
   
   The predicate maps `A` to `Prop` in the same universe as `A`, hence the predicate is 
   in the same universe as `A`. `Prop` can be mapped into other universes using `ulift` 
   and `prop_resize`, if we assume the resizing axiom. -/
@[hott]
def Subset (A : Set.{u}) := A -> trunctype.{u} -1
   
@[hott]
instance (A : Set.{u}) : has_coe_to_sort (Subset A) := 
  has_coe_to_sort.mk Type.{u} (λ B, Σ a : A, B a)

@[hott]
instance {A : Set} (B : Subset A) : has_coe ↥B ↥A :=
  ⟨λ b, b.1⟩

/- The type of all subsets of a set `A` is a set: the power set of `A`. -/
@[hott, instance]
def Powerset_is_set {A : Set} : is_set (Subset A) := 
begin
  fapply is_set.mk, intros B C p q,
  have eq_eqv_hom : (B = C) ≃ (B ~ C), from eq_equiv_homotopy B C,
  have is_prop_hom : is_prop (B ~ C), from 
    have pP : forall a : A, is_prop (B a = C a), from 
      assume a, is_trunc_eq -1 (B a) (C a),
    @is_prop_dprod _ (λ a : A, B a = C a) pP,  
  have H_eqv : is_prop (B = C), from 
    is_trunc_is_equiv_closed -1 (equiv.to_fun eq_eqv_hom)⁻¹ᶠ is_prop_hom, 
  exact @is_prop.elim _ H_eqv p q
end  

@[hott, reducible]
def Powerset (A : Set) : Set :=
  Set.mk (Subset A) Powerset_is_set

hott_theory_cmd "local prefix `𝒫`:100 := hott.subset.Powerset"    


/- Categorically spoken, we have defined subsets by the characteristic map to a 
   subobject classifier in the category of sets. This is usually a much more effective 
   way of dealing with subobjects in a category than using the structure of a subobject
   directly. However, we also introduce this structure, and show its equivalence with the
   original definition, for later use in the category of sets. 
   
   Note also that replacing `Prop` by `Two` in the subobject classifier only leads to
   equivalent notions of subsets if `LEM` is assumed. Otherwise, only constructible 
   subsets defined by decidable predicates are considered. -/
@[hott]
structure inj_Subset (A : Set.{u}) :=
   (carrier : Set.{u}) (map : carrier -> A)  (inj : is_set_injective map) 

/- We first produce sets and injective maps from predicates. -/
@[hott, instance]
def is_set_pred {A : Set.{u}} : Π (B : Subset A), is_set (Σ (a : A), B a) :=
  assume B, 
  have forall (a : A), is_set (B a), from 
    assume a, 
    have is_prop (B a), from trunctype.struct (B a),
    is_trunc_succ (B a) -1, 
  is_trunc_sigma (λ a : A, B a) 0 

@[hott]
def pred_Set {A : Set.{u}} (B : Subset A) : Set :=
  Set.mk (Σ (a : A), B a) (is_set_pred B)  

@[hott] 
def pred_Set_map {A : Set.{u}} (B : Subset A) : pred_Set B -> A := λ b, b.1  

@[hott]
def pred_Set_map_is_inj {A : Set.{u}} (B : Subset A) : 
  is_set_injective (pred_Set_map B) :=
begin 
  intros b₁ b₂ H, fapply sigma_eq, 
  { exact H }, 
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

/- Next, we construct maps between the two types of subsets, and show that they are 
   inverse to each other.-/
@[hott]
def pred_to_inj_sset {A : Set.{u}} : Subset A -> inj_Subset A :=
  assume B,
  inj_Subset.mk (pred_Set B) (pred_Set_map B) (pred_Set_map_is_inj B) 

@[hott]
def inj_to_pred_sset {A : Set.{u}} : inj_Subset A -> Subset A :=
  assume B_inj,
  assume a, image B_inj.map a 

@[hott]
def inj_car_eqv_pred_sset {A : Set.{u}} {B_car : Set.{u}} (map : B_car -> A) 
  (inj : is_set_injective map) : 
  pred_Set (λ a : A, image map a) ≃ B_car :=
let HP : (Σ a : A, (image map a)) -> (Σ a : A, fiber map a) := λ a_im, ⟨a_im.1, 
  @untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib map inj a_im.1) a_im.2⟩ in
have H : ∀ a_im : (Σ a : A, image map a), map (HP a_im).2.1 = a_im.1, from
  assume a_im, (HP a_im).2.2,             
let f : (Σ a : A, image map a) -> B_car := λ a_im, (HP a_im).2.1 in
let g : B_car -> (Σ a : A, image map a) := λ b, ⟨map b, tr ⟨b, idp⟩⟩ in  
have rinv : ∀ b : B_car, f (g b) = b, from 
  assume b,
  calc f (g b) = (HP (g b)).2.1 : rfl
       ... = b : ap fiber.point (@is_prop.elim _ (set_inj_implies_unique_fib map inj (map b))
                                 (fiber.mk (HP (g b)).2.1 (H (g b))) (fiber.mk b idp)),
have linv : ∀ (a_im : Σ a : A, image map a), g (f a_im) = a_im, from 
  begin 
    intro a_im, fapply sigma_eq,
    { calc (g (f a_im)).1 = map (f a_im) : rfl
           ... = a_im.1 : H a_im },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
  end,
equiv.mk f (adjointify f g rinv linv) 

@[hott]
def pred_sset_linv {A : Set.{u}} (B_inj : inj_Subset A) : 
  pred_to_inj_sset (inj_to_pred_sset B_inj) = B_inj :=
begin
  hinduction B_inj,
  change inj_Subset.mk (pred_Set (λ a : A, image map a)) (λ b, b.1) _ =
         inj_Subset.mk carrier map inj,
  fapply apd0111 inj_Subset.mk,
  { apply car_eq_to_set_eq,
    exact ua (inj_car_eqv_pred_sset map inj) },
  { apply pathover_of_tr_eq, apply eq_of_homotopy, intro b,
    let H : ∀ A₁ A₂ : Set, is_equiv (@ap _ _ trunctype.carrier A₁ A₂) := 
      assume A₁ A₂, (@set_eq_equiv_car_eq A₁ A₂).to_is_equiv,
    have H' : @car_eq_to_set_eq (pred_Set (λ (a : ↥A), image map a)) carrier = 
              @is_equiv.inv _ _ _ (H _ carrier), from rfl,
    rwr H',          
    calc _ = (ua (inj_car_eqv_pred_sset map inj) ▸[λ C : Type _, C -> A.carrier]
                 (λ (b : ↥(pred_Set (λ (a : ↥A), image map a))), b.fst)) b : 
               ap_inv_po_fn (λ (b : (pred_Set (λ (a : ↥A), 
                                image map a)).carrier), b.fst) H b
                                (ua (inj_car_eqv_pred_sset map inj)) 
         ... = (λ (b : (pred_Set (λ (a : ↥A), image map a)).carrier), b.fst)
                 ((ua (inj_car_eqv_pred_sset map inj))⁻¹ ▸[λ C : Type _, C] b) : 
               tr_fn_eval_tr _ b
         ... = (cast (ua (inj_car_eqv_pred_sset map inj))⁻¹ b).fst : rfl
         ... = ((inj_car_eqv_pred_sset map inj)⁻¹ᶠ b).fst : by rwr cast_ua_inv
         ... = map b : rfl },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end            

@[hott]
def pred_sset_rinv {A : Set.{u}} (B : Subset A) :
  inj_to_pred_sset (pred_to_inj_sset B) = B :=
begin
  apply eq_of_homotopy, intro a,
  change image (λ b : pred_Set B, b.1) a = B a,
  fapply prop_iff_eq,
  { intro p, 
    let a_fib : fiber (λ (b : ↥(pred_Set B)), b.fst) a := 
      @untrunc_of_is_trunc _ _ (set_inj_implies_unique_fib (λ (b : ↥(pred_Set B)), b.fst) 
        (pred_to_inj_sset B).inj a) p,
    have H : a = a_fib.1.1, by from (a_fib.2)⁻¹,
    rwr H, exact a_fib.1.2 },
  { intro p, apply tr, exact ⟨⟨a,p⟩, idp⟩ }
end  

@[hott]
def pred_eqv_inj_sset {A : Set.{u}} : (Subset A) ≃ (inj_Subset A) :=
  equiv.mk pred_to_inj_sset (adjointify pred_to_inj_sset inj_to_pred_sset
                                        pred_sset_linv pred_sset_rinv) 

/- On subsets we can introduce the `∈`-notation and the `⊆`-notation of set theory. -/
@[hott]
protected def elem {A : Set} (a : A) (S : Subset A) :=
  S a

@[hott, instance]
def set_mem {A : Set} : @has_mem A (Subset A) :=
  has_mem.mk (λ (a : A) (S : Subset A), subset.elem a S)

notation `{ ` binder ` ∈ ` B ` | ` P:scoped  ` }` := (P : Subset B)
notation `{ ` binder ` ∈ ` B ` | ` P:scoped  ` }` := (P : Subset (to_Set B)) 

/- For sets the form of LEM needed is decidability for the element relation for arbitrary
   subsets. However, even when just assumed for finite sets this is equivalent to LEM, see
   the article of Andrej Bauer on constructivism and [sets.axioms]. But the element 
   relation becomes decidable in decidable subsets, that is, subsets defined as 
   predicates with values equal to True or False (which are of course subsets in the 
   sense above). 
   
   We define a class `has_dec_elem` indicating that the element relation is decidable in 
   a set. If an instance of this class holds, we show that all subsets are decidable and
   hence the element relation is decidable. -/
@[hott]
class has_dec_elem (A : Set) := 
  (dec_el : Π (a : A) (S : Subset A), (a ∈ S) ⊎ ¬(a ∈ S))

@[hott]
def Two_pred_to_sset {A : Set.{u}} :
  (A -> Two.{u}) -> Subset A :=
begin intros S a, exact @Two.rec (λ t, Prop) False True (S a) end

@[hott]
def Two_pred_sset_is_dec {A : Set.{u}} {P : A -> Two.{u}} :
  Π (a : A), Two_pred_to_sset P a ⊎ ¬(Two_pred_to_sset P a) :=
begin
  intro a, 
  change @Two.rec (λ t, Prop) False True (P a) ⊎ ¬(@Two.rec (λ t, Prop) False True (P a)), 
  hinduction P a with T F,
    apply sum.inr, intro f, hinduction f, 
    apply sum.inl, exact true.intro
end

@[hott]
def sset_to_Two_pred_sset {A : Set.{u}} [H : has_dec_elem A] : 
  Subset A -> (A -> Two.{u}) :=
begin 
  intros S a, exact @sum.rec (a ∈ S) (¬(a ∈ S)) (λ s, Two) (λ v, Two.one) 
                             (λ v, Two.zero) (@has_dec_elem.dec_el A H a S) 
end

@[hott]
def sset_Two_pred_sset_linv (A : Set.{u}) [H : has_dec_elem A] : Π (S : Subset A), 
  Two_pred_to_sset (sset_to_Two_pred_sset S) = S :=
begin
  intro S, apply eq_of_homotopy, intro a, 
  change @Two.rec (λ t, Prop) False True ((sset_to_Two_pred_sset S) a) = _, 
  hinduction @has_dec_elem.dec_el A H a S with p val, 
    { change @Two.rec (λ t, Prop) _ _ 
                 (@sum.rec (a ∈ S) (¬(a ∈ S)) (λ s, Two) _ _ 
                           (@has_dec_elem.dec_el A H a S)) = _, 
      rwr p, change True = _, fapply inhabited_Prop_eq, exact true.intro, exact val }, 
    { change @Two.rec (λ t, Prop) _ _ 
                 (@sum.rec (a ∈ S) (¬(a ∈ S)) (λ s, Two) _ _ 
                           (@has_dec_elem.dec_el A H a S)) = _, 
      rwr p, change False = _, fapply uninhabited_Prop_eq, intro f, hinduction f, 
      exact val } 
end

@[hott]
def sset_Two_pred_sset_rinv (A : Set.{u}) [H : has_dec_elem A] : Π (S : A -> Two.{u}), 
  sset_to_Two_pred_sset (Two_pred_to_sset S) = S :=
begin
  intro S, apply eq_of_homotopy, intro a,
  let S' : Subset A := λ a, @Two.rec (λ t, Prop) False True (S a),
  change @sum.rec (a ∈ S') (¬(a ∈ S')) (λ s, Two) (λ v, Two.one) 
            (λ v, Two.zero) (@has_dec_elem.dec_el A H a (λ a, S' a)) = _,
  hinduction S a with p, 
  { have q : S' a = False, from 
      begin change @Two.rec (λ t, Prop) False True (S a) = _, rwr p end,
    hinduction @has_dec_elem.dec_el A H a (λ a, S' a) with q', hinduction q ▸ val, refl },
  { have q : S' a = True, from 
      begin change @Two.rec (λ t, Prop) False True (S a) = _, rwr p end,
    hinduction @has_dec_elem.dec_el A H a (λ a, S' a) with q', refl, 
    have v' : ↥(S' a), from (ap trunctype.carrier q)⁻¹ ▸[id] true.intro, 
    hinduction val v' }
end

/- Correspondence of element relation and predicate. -/
@[hott, reducible]
def pred_elem {A : Set} {P : Subset A} (a : A) : a ∈ { a ∈ A | P a } <-> P a :=
  have imp₁ : a ∈ { a ∈ A | P a } -> P a, from
    begin intro elem_a_P, exact elem_a_P end,
  have imp₂ : P a -> a ∈ { a ∈ A | P a }, from
    begin intro pred_a, exact pred_a end,  
  ⟨imp₁, imp₂⟩ 

@[hott]
def elem_to_pred {A : Set} {P : Subset A} (a : A) : a ∈ { a ∈ A | P a } -> P a :=
begin intro elem_a_P, exact elem_a_P end

@[hott]
def pred_to_elem {A : Set} {P : Subset A} (a : A) : P a -> a ∈ { a ∈ A | P a } :=
begin intro pred_a, exact pred_a end 

@[hott]   
inductive construct_elem {A : Set} (P : A → trunctype -1) 
| intro (w : A) (h : P w) : construct_elem

attribute [intro] construct_elem.intro

@[hott]
def exists_elem {A : Set} (P : A → Prop) : Prop :=
  ∥ construct_elem P ∥ 

notation `∃` binder `∈` B `,` P:scoped := @exists_elem B P 

@[hott]
def unique_elem {A : Set} (P : A → Prop) := (Σ a : A, P a) × is_prop (Σ a : A, P a)

notation `∃!` binder `∈` B `,` P:scoped := @unique_elem B P 

@[hott]
def unique_to_elem {A : Set} (P : A → Prop) (ue : unique_elem P) : A := ue.1.1

@[hott]
def unique_to_pred {A : Set} (P : A → Prop) (ue : unique_elem P) : P (unique_to_elem P ue) :=
  ue.1.2

@[hott]
def unique_to_uniq {A : Set} (P : A → Prop) (ue : unique_elem P) : is_prop (Σ a : A, P a) :=
  ue.2

@[hott]
def is_subset_of {A : Set.{u}} (B C : Subset A) :=
  forall a : A, a ∈ B -> a ∈ C

@[hott, instance]
def is_prop_subset {A : Set.{u}} (B C : Subset A) : is_prop (is_subset_of B C) :=
  have Pss : ∀ a : A, is_prop (a ∈ B -> a ∈ C), from 
    assume a, is_prop_map ((a ∈ C).struct),
  is_prop_dprod Pss

@[hott, instance]
def set_has_Subsets {A : Set.{u}} : @has_subset (Subset A) :=
  has_subset.mk (λ B C : Subset A, Prop.mk (is_subset_of B C) (is_prop_subset B C))

@[hott]
def pred_Set_inc {A : Set.{u}} {B C : Subset A} (inc : B ⊆ C) : 
  pred_Set B -> pred_Set C :=
begin intro b, exact ⟨b.1, inc b.1 b.2⟩ end


/- We show some basic facts on subsets. 

   Two subsets are equal iff they are subsets of each other. -/
@[hott]
def sset_eq_iff_inclusion {A : Set.{u}} (B C : Subset A) :
  B = C ↔ (B ⊆ C) × (C ⊆ B) :=
have imp1 : B = C -> (B ⊆ C) × (C ⊆ B), from 
  assume sset_eq, 
  have incl1 : B ⊆ C, from assume a a_in_B,
    sset_eq ▸[λ D : Subset A, ↥(a ∈ D)] a_in_B,
  have incl2 : C ⊆ B, from assume a a_in_C,
    sset_eq⁻¹ ▸[λ D : Subset A, ↥(a ∈ D)] a_in_C, 
  prod.mk incl1 incl2, 
have imp2 : (B ⊆ C) × (C ⊆ B) -> B = C, from 
  assume incl, let incl1 := prod.fst incl, incl2 := prod.snd incl in 
  begin 
    apply eq_of_homotopy, intro a, fapply prop_iff_eq, 
    { exact incl1 a },
    { exact incl2 a } 
  end,
prod.mk imp1 imp2

/- A criterion for not being a subset -/
@[hott]
def not_ss_elem {A : Set} (B₁ B₂ : Subset A) : 
  Not (B₁ ⊆ B₂) <-> ∃ a ∈ A, a ∈ B₁ and Not (a ∈ B₂) :=
begin 
  apply pair,
  { intro not_ss, 
    have ex_not_imp : ↥∥Σ a : A, Not (to_Prop (a ∈ B₁ -> a ∈ B₂))∥, from 
      (not_all _).1 not_ss, 
    hinduction ex_not_imp with eni, 
    apply tr, fapply construct_elem.intro, 
    { exact eni.1 },
    { exact (neg_imp _ _).1 eni.2 } },
  { intros ex Bss, hinduction ex with cons, hinduction cons with a' Pa, 
    exact (neg_imp _ _).2 Pa (Bss a') }
end

/- Two subsets that always exist. -/
@[hott]
def total_Subset (A : Set.{u}) : Subset A := 
  λ a, True.{u}

@[hott]
def all_elem {A : Set} (a : A) : a ∈ total_Subset A :=
  true.intro

@[hott]
def total_pred_Set_eq_Set (A : Set) : pred_Set (total_Subset A) = A :=
begin 
  apply bij_to_set_eq, fapply has_inverse_to_bijection, 
  { intro a_pred, exact a_pred.1 },
  { intro a, exact ⟨a, true.intro⟩ },
  { fapply is_set_inverse_of.mk, 
    { intro a, refl },
    { intro a_pred, fapply sigma_eq,
      { refl },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end     

@[hott]   
def empty_Subset (A : Set.{u}) : Subset A :=
  λ a, False.{u}

@[hott]
def empty_not_elem {A : Set} (a : A) : a ∉ empty_Subset A :=
begin intro el_a, hinduction el_a end  

/- Singleton subsets containing one element of a set -/
@[hott]
def singleton_sset {A : Set} (a : A) : Subset A :=
  λ b : A, to_Prop (b = a) 

/- The image subset (of a subset) under a map between sets. The sets lie in the 
   same universe. -/
@[hott]
def ss_Image {A B : Set.{u}} (f : A -> B) (C : Subset A) : Subset B := 
  λ b : B, image (f ∘ (pred_Set_map C)) b 

@[hott]
def Image {A B : Set.{u}} (f : A -> B) : Subset B :=
  ss_Image f (total_Subset A)

/- Some lemmas to exploit the image of a subset under a map. -/
@[hott]
def ss_image_preimage {A B : Set.{u}} (f : A -> B) (C : Subset A) : 
  ∀ b : B, b ∈ ss_Image f C -> image (f ∘ (pred_Set_map C)) b :=
begin intros b el, hinduction el with fa, exact tr fa end   

@[hott]
def ss_image_el {A B : Set.{u}} (f : A -> B) (C : Subset A) : 
  ∀ (a : A), a ∈ C -> f a ∈ ss_Image f C :=
begin 
  intros a ela, 
  apply tr, fapply fiber.mk, 
  { exact ⟨a, ela⟩ },
  { exact idp } 
end

@[hott]
def ss_im_preim_el {A B : Set} (f : A -> B) (C : Subset A) (b : B) :
  b ∈ ss_Image f C -> ∥Σ a : A, (a ∈ C) × (f a = b)∥ :=
begin 
  intro elb,
  have imb : ↥(image (f ∘ (pred_Set_map C)) b), from ss_image_preimage f C b elb,
  hinduction imb with fibb,
  exact tr ⟨(pred_Set_map C) fibb.1, ⟨fibb.1.2, fibb.2⟩⟩
end 

@[hott]
def ss_im_comp {A B C : Set} (f : A -> B) (g : B -> C) (D : Subset A) :
  ∀ c : C, c ∈ ss_Image g (ss_Image f D) <-> c ∈ ss_Image (g ∘ f) D :=
begin 
  intro c, apply pair,
  { intro elc, 
    let imc := ss_image_preimage g (ss_Image f D) c elc,
    hinduction imc with fibc,
    let b := (pred_Set_map (ss_Image f D)) fibc.1,
    have elb : ↥(b ∈ ss_Image f D), from fibc.1.2,
    let ima := ss_im_preim_el f D b elb,
    hinduction ima with H, let a := H.1,
    have p : c = g (f a), by rwr H.2.2; rwr <- fibc.2, 
    rwr p, exact ss_image_el (g ∘ f) D a H.2.1 },
  { intro elc, 
    let ima := ss_im_preim_el (g ∘ f) D c elc,
    hinduction ima with H, let a := H.1, let b := f a,
    rwr <- H.2.2, change ↥((g b)∈ss_Image g (ss_Image f D)),
    exact ss_image_el g (ss_Image f D) b (ss_image_el f D a H.2.1) }
end  

/- A criterion for a type to be a set: it is mapped injectively to a set. 
   The proof needs a fact that is already shown for sets in [sets.basic]: fibers of 
   injective maps only contain one element. -/
@[hott]
def inj_implies_unique_fib {A : Set} {B : Type _} (f : B -> A) : 
  (∀ b₁ b₂ : B, f b₁ = f b₂ -> b₁ = b₂) -> ∀ a : A, is_prop (fiber f a) :=
assume f_inj a,
have H : forall fb1 fb2 : fiber f a, fb1 = fb2, from
  assume fb1 fb2,
  match fb1, fb2 with fiber.mk b1 e1, fiber.mk b2 e2 :=    
    have eqb : b1 = b2, from f_inj b1 b2 (e1 ⬝ e2⁻¹), 
    have eqbeq : e1 =[eqb;(λ b : B, f b = a)] e2, from pathover_of_tr_eq (is_set.elim _ _),
    apd011 fiber.mk eqb eqbeq 
  end,  
is_prop.mk H 

@[hott]
def inj_to_Set_is_set (A : Type _) {B : Set} {f : A -> B} 
  (inj_f : ∀ a₁ a₂ : A, f a₁ = f a₂ -> a₁ = a₂) : is_set A :=
begin
  let Im_f := pred_Set (λ b : B, image f b),
  have A_eqv_Im_f : A ≃ Im_f, from 
  begin
    fapply equiv.MK, 
    { intro a, fapply sigma.mk, exact f a, apply tr, exact fiber.mk a idp },
    { intro b_im, exact (@untrunc_of_is_trunc _ _ (inj_implies_unique_fib f inj_f b_im.1) 
                                              b_im.2).1 },
    { intro b_im, fapply sigma_eq,
      { exact (@untrunc_of_is_trunc _ _ (inj_implies_unique_fib f inj_f b_im.1) b_im.2).2 }, 
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intro a, change _ = (@fiber.mk _ _ f (f a) a idp).point, apply ap fiber.point, 
      exact @is_prop.elim _ (inj_implies_unique_fib f inj_f (f a)) _ _ }
  end,
  apply is_trunc_equiv_closed_rev, apply A_eqv_Im_f, apply_instance
end  

end subset

end hott