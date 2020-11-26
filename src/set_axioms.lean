import hott.init hott.types.trunc prop_logic

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open is_trunc trunc equiv is_equiv

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
    have trunc_pi : ∥ Π (x : X), Σ (a : A x), P x a ∥, from 
      AxCh_ne X (λ (x : X), Σ (a : A x), P x a) pi_trunc,
    sorry,
  (imp1, imp2)

end hott