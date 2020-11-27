import hott.init hott.types.trunc prop_logic

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open hott.is_trunc hott.trunc hott.equiv hott.is_equiv hott.sigma 

/- This is contained as [is_set_pred] in [subset.lean]. But we want to avoid
   dependencies.  -/
@[hott]   
def Sigma_Set_Prop_is_set (X : Set.{u}) (P : X -> trunctype.{u} -1) : 
  is_set (Σ x : X, P x) := 
have forall (x : X), is_set (P x), from 
  assume x, 
  have is_prop (P x), from trunctype.struct (P x),
  is_trunc_succ (P x) -1, 
is_trunc_sigma (λ x : X, ↥(P x)) 0    

/- The two versions of the Axiom of Choice, as presented in the HoTT-Book, (3.8.1)
   and (3.8.3). By Lem.3.8.2, the two are equivalent. -/
@[hott]
def AxChoice := Π (X : Set.{u}) (A : X -> Set.{u}) 
  (P: Π x : X, A x -> trunctype.{u} -1),
(forall x : X, ∥ Σ a : A x, P x a ∥) -> ∥ Σ (g : Π x : X, A x), forall x : X, P x (g x) ∥   

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
    have pi_trunc_T : Π x : X, ∥ Σ y : Y x, True ∥, from sorry,
    have trunc_sigma_T : ∥ Σ (g : Π x : X, Y x), ∀ x : X, True ∥, from 
      AxCh X Y (λ x : X, λ y : Y x, True) pi_trunc_T,   
    sorry,
  have imp2 : AxChoice_nonempty -> AxChoice, from 
    assume AxCh_ne, assume X A P pi_trunc, 
    have sigma_P_is_set : Π x : X, is_set (Σ (a : A x), P x a), from 
      assume x, Sigma_Set_Prop_is_set (A x) (P x),
    let Sigma_P := λ x, Set.mk (Σ (a : A x), P x a) (sigma_P_is_set x) in 
    have trunc_pi : ∥ Π (x : X), Σ (a : A x), P x a ∥, from 
      AxCh_ne X Sigma_P pi_trunc,
    sorry,
  (imp1, imp2)

end hott