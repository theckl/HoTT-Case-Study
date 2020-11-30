import hott.init hott.types.trunc hott.homotopy.susp prop_logic

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open hott.is_trunc hott.trunc hott.equiv hott.is_equiv hott.sigma 

/- Looks like a HoTT-ism but is a way to construct sets - which can be interpreted
   as subsets. Therefore it is also contained as [is_set_pred] in [subset.lean]. 
   But we want to avoid dependencies.  -/
@[hott]   
def Sigma_Set_Prop_is_set (X : Set.{u}) (P : X -> trunctype.{u} -1) : 
  is_set (Σ x : X, P x) := 
have forall (x : X), is_set (P x), from 
  assume x, 
  have is_prop (P x), from trunctype.struct (P x),
  is_trunc_succ (P x) -1, 
is_trunc_sigma (λ x : X, ↥(P x)) 0    

/- The two versions of the Axiom of Choice, as presented in the HoTT-Book, (3.8.1)
   and (3.8.3). We postulate both as axioms, to keep track of their use, even if by 
   Lem.3.8.2, the two are equivalent. -/
@[hott]
def AxChoice := Π (X : Set.{u}) (A : X -> Set.{u}) 
  (P: Π x : X, A x -> trunctype.{u} -1),
(forall x : X, ∥ Σ a : A x, P x a ∥) -> ∥ Σ (g : Π x : X, A x), Π x : X, P x (g x) ∥   

@[hott]
axiom AC : AxChoice

@[hott]
def AxChoice_nonempty := Π (X : Set.{u}) (Y : X -> Set.{u}), 
  (Π x : X, ∥ Y x ∥) -> ∥ Π x : X, Y x ∥ 

@[hott]
axiom AC_nonempty : AxChoice_nonempty

@[hott]
lemma AxChoice_equiv : AxChoice.{u} ↔ AxChoice_nonempty.{u} :=
  have imp1 : AxChoice.{u} -> AxChoice_nonempty.{u}, from 
    assume AxCh, assume X Y pi_trunc, 
    have pi_trunc_T : Π x : X, ∥ Σ y : Y x, True ∥, from 
      assume x, trunc_functor -1 (λ y : Y x, ⟨y,true.intro⟩) (pi_trunc x),
    have trunc_sigma_T : ∥ Σ (g : Π x : X, Y x), ∀ x : X, True ∥, from 
      AxCh X Y (λ x : X, λ y : Y x, True) pi_trunc_T, 
    have sigma_pi_T : (Σ (g : Π x : X, Y x), ∀ x : X, True) -> (Π x : X, Y x), from
      assume sigma_T, sigma_T.1,    
    trunc_functor -1 sigma_pi_T trunc_sigma_T,
  have imp2 : AxChoice_nonempty -> AxChoice, from 
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
@[hott]
def LawExcludedMiddle := Π (A : Type u) [is_prop A], A ⊎ ¬ A

@[hott]
axiom LEM : LawExcludedMiddle

/- We follow the proof of Diaconescu (HoTT-book, Thm.10.1.14) to show that the Axiom 
   of Choice (in its second version [AxChoice_nonempty]) implies the Law of the Excluded 
   Middle. 
   
   The first step is a lemma stating that the suspension (see HoTT-book, Sec.6.5) of a 
   mere proposition is a set. -/
@[hott]
def susp_of_prop_is_set (A : Type u) [is_prop A] : is_set (susp A) :=
  sorry

@[hott] 
def AC_implies_LEM : AxChoice_nonempty -> LawExcludedMiddle :=
  sorry

end hott