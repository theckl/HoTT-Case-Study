import hott.init hott.types.trunc

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open is_trunc trunc equiv is_equiv

/- The two versions of the Axiom of Choice, as presented in the HoTT-Book, (3.8.1)
   and (3.8.3). By Lem.3.8.2, the two are equivalent. -/
@[hott]
axiom AC (X : Set.{u}) (A : X -> trunctype.{u} -1) 
  (P: Π x : X, A x -> trunctype.{u} -1) :
(forall x : X, ∥ Σ a : A x, P x a ∥) -> ∥ Σ (g : Π x : X, A x), forall x : X, P x (g x) ∥   

@[hott]
axiom AC_var (X : Set.{u}) (Y : X -> Set.{u}) : 
  (Π x : X, ∥ Y x ∥) -> ∥ Π x : X, Y x ∥ 

end hott