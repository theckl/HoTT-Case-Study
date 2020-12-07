import hott.init hott.types.trunc hott.homotopy.susp prop_logic

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open hott.is_trunc hott.trunc hott.equiv hott.is_equiv hott.sigma hott.susp

/- Should be in a separate section/file in the folder [types]. 
   [Zero] and [One] are equivalent to [true] and [false] in [prop_logic], but
   we want to use them without logical connotations. -/
@[hott]
inductive Zero : Type _

@[hott]
def eq_Zero : forall f₁ f₂ : Zero, f₁ = f₂ :=
begin
  intros,
  induction f₁,
end  

@[hott, instance]
def is_prop_Zero : is_prop Zero :=
  is_prop.mk eq_Zero 

@[hott]
inductive One : Type _  
| star : One

@[hott]
def eq_One : forall t₁ t₂ : One, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl One.star),
end 

@[hott, instance]
def One_is_prop : is_prop One :=
  is_prop.mk eq_One

@[hott]
inductive Two : Type _ 
| zero : Two 
| one : Two 

/- We prove that [Two] is a set using the encode-decode method presented in the
   HoTT-book, Sec.2.13. -/
@[hott]
def code_Two : Two.{u} -> Two.{u} -> Type.{u} :=
begin
  intros t₁ t₂, 
  induction t₁,
    induction t₂, exact One, exact Zero,
    induction t₂, exact Zero, exact One,
end  

@[hott, simp]
def encode_Two : Π t₁ t₂ : Two, (t₁ = t₂) -> code_Two t₁ t₂ :=
  have r : Π t : Two, code_Two t t, by 
    intro t; induction t; exact One.star; exact One.star,
  assume t₁ t₂ eq, transport (λ t : Two, code_Two t₁ t) eq (r t₁)

@[hott, simp]
def decode_Two : Π t₁ t₂ : Two, code_Two t₁ t₂ -> (t₁ = t₂) :=
begin
  intros t₁ t₂,
  induction t₁, 
    induction t₂, intro; refl, intro f; induction f,
    induction t₂, intro f; induction f, intro; refl,     
end    

@[hott]
def Two_eq_equiv_code : ∀ t₁ t₂ : Two, (t₁ = t₂) ≃ code_Two t₁ t₂ := 
  sorry 

@[hott, instance]
def Two_is_set : is_set Two.{u} :=
  have Two_eq_is_prop : ∀ t₁ t₂ : Two.{u}, is_prop (t₁ = t₂), from 
    assume t₁ t₂,
    have code_Two_is_prop : is_prop (code_Two t₁ t₂), from
      sorry,
    is_trunc_equiv_closed_rev -1 (Two_eq_equiv_code t₁ t₂) code_Two_is_prop,
  is_trunc_succ_intro Two_eq_is_prop

@[hott]
def Two_Set : Set :=
  Set.mk Two Two_is_set   

/- Looks like a HoTT-ism but is a way to construct sets - which can be interpreted
   as subsets. Therefore it is also contained as [is_set_pred] in [subset.lean]. 
   But we want to avoid dependencies.  -/
@[hott, instance]   
def Sigma_Set_Prop_is_set (X : Set.{u}) (P : X -> trunctype.{u} -1) : 
  is_set (Σ x : X, P x) := 
have forall (x : X), is_set (P x), from 
  assume x, 
  have is_prop (P x), from trunctype.struct (P x),
  is_trunc_succ (P x) -1, 
is_trunc_sigma (λ x : X, ↥(P x)) 0    

@[hott, instance]
def fib_set_map_is_set {A B : Set.{u}} (f : A -> B) (b : B) : is_set (fiber f b) :=
  have sig_fib_is_set : is_set (Σ a : A, f a = b), from 
    let P := λ a : A, Prop.mk (f a = b) (is_prop.mk (@is_set.elim _ _ (f a) b)) in
    Sigma_Set_Prop_is_set A P,
  is_trunc_equiv_closed_rev 0 (fiber.sigma_char f b) sig_fib_is_set 

/- The two versions of the Axiom of Choice, as presented in the HoTT-Book, (3.8.1)
   and (3.8.3). We postulate both as axioms, to keep track of their use, even if by 
   Lem.3.8.2, the two are equivalent. -/
@[hott]
def Choice := Π (X : Set.{u}) (A : X -> Set.{u}) 
  (P: Π x : X, A x -> trunctype.{u} -1),
(forall x : X, ∥ Σ a : A x, P x a ∥) -> ∥ Σ (g : Π x : X, A x), Π x : X, P x (g x) ∥   

@[hott]
axiom AC : Choice

@[hott]
def Choice_nonempty := Π (X : Set.{u}) (Y : X -> Set.{u}), 
  (Π x : X, ∥ Y x ∥) -> ∥ Π x : X, Y x ∥ 

@[hott]
axiom AC_nonempty : Choice_nonempty

@[hott]
lemma AxChoice_equiv : Choice.{u} ↔ Choice_nonempty.{u} :=
  have imp1 : Choice.{u} -> Choice_nonempty.{u}, from 
    assume AxCh, assume X Y pi_trunc, 
    have pi_trunc_T : Π x : X, ∥ Σ y : Y x, True ∥, from 
      assume x, trunc_functor -1 (λ y : Y x, ⟨y,true.intro⟩) (pi_trunc x),
    have trunc_sigma_T : ∥ Σ (g : Π x : X, Y x), ∀ x : X, True ∥, from 
      AxCh X Y (λ x : X, λ y : Y x, True) pi_trunc_T, 
    have sigma_pi_T : (Σ (g : Π x : X, Y x), ∀ x : X, True) -> (Π x : X, Y x), from
      assume sigma_T, sigma_T.1,    
    trunc_functor -1 sigma_pi_T trunc_sigma_T,
  have imp2 : Choice_nonempty -> Choice, from 
    assume AxCh_ne, assume X A P pi_trunc, 
    have sigma_P_is_set : Π x : X, is_set (Σ (a : A x), P x a), from 
      assume x, Sigma_Set_Prop_is_set (A x) (P x),
    let Sigma_P := λ x, Set.mk (Σ (a : A x), P x a) (sigma_P_is_set x) in 
    have trunc_pi : ∥ Π (x : X), Σ (a : A x), P x a ∥, from 
      AxCh_ne X Sigma_P pi_trunc,
    have pssp : (Π (x : X), Σ (a : A x), P x a) -> (Σ (g : Π x : X, A x), Π x : X, P x (g x)), from
      (sigma_pi_equiv_pi_sigma (λ (x : X) (a : A x), ↥(P x a)))⁻¹ᶠ,   
    trunc_functor -1 pssp trunc_pi,
  (imp1, imp2)

/- The Law of the Excluded Middle, following the HoTT-book, (3.4.1) -/
def ExcludedMiddle := Π (A : trunctype.{u} -1), A ⊎ ¬ A

@[hott]
axiom LEM : ExcludedMiddle

/- We follow the proof of Diaconescu (HoTT-book, Thm.10.1.14) to show that the Axiom 
   of Choice (in its second version [AxChoice_nonempty]) implies the Law of the Excluded 
   Middle. 
   
   The first step is a lemma stating that the suspension (see HoTT-book, Sec.6.5) of a 
   mere proposition is a set. -/
@[hott]
def susp_of_prop_is_set (A : Type u) [is_prop A] : is_set (⅀ A) :=
  sorry

@[hott] 
def AC_implies_LEM : Choice_nonempty.{u} -> ExcludedMiddle.{u} :=
  assume AC, assume A, 
  let f := λ pt : Two.{u}, @Two.rec (λ t : Two, ⅀ A) (@north A) (@south A) pt in 
  have zn : f Two.zero = north, by refl,
  have zs : f Two.one = south, by refl,
  have f_is_surj : @is_surjective Two (⅀ A) f, from 
    have PN : @image Two (⅀ A) f north, from @image.mk Two (⅀ A) f _ Two.zero zn,
    have PS : @image Two (⅀ A) f south, from @image.mk Two (⅀ A) f _ Two.one zs,
    have Pm : Π a : A, PN =[merid a; λ x : susp A, @image Two (⅀ A) f x] PS, from 
      assume a, pathover_prop_eq _ (merid a) PN PS,
    assume x, susp.rec PN PS Pm x,
  let X := Set.mk (⅀ A) (susp_of_prop_is_set A),
      Y := λ x : X, Set.mk (@fiber Two (⅀ A) f x) (@fib_set_map_is_set Two_Set X f x) in 
  have mere_g : ∥ Π x : X, @fiber Two (⅀ A) f x ∥, from AC X Y f_is_surj,  
  sorry

end hott