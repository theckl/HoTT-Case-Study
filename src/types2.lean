import hott.init hott.hit.trunc hott.types.trunc

universes u v w
hott_theory

namespace hott
open hott.is_trunc hott.trunc

/- Properties of the product of two types -/
@[hott]
def all_prod_all {I J : Type _} (F : I -> J -> Type _) : 
  (∀ p : I × J, F p.1 p.2) -> ∀ (i : I) (j : J), F i j :=
assume all_prod i j, all_prod ⟨i,j⟩  

#print trunc.elim

/- An extended elimination principle for truncations -/
@[hott]
def trunc.elim2 {n : ℕ₋₂} {A : Type _} {B : Type _} {P : Type _} [Pt : is_trunc n P] : 
  (A → B -> P) → trunc n A → trunc n B -> P :=
begin intros f tA tB, exact untrunc_of_is_trunc (trunc_functor2 f tA tB) end  

@[hott]
def sigma_Prop_eq {A : Type _} {B : Π a : A, Prop} (s₁ s₂ : Σ (a : A), B a) : 
  s₁.1 = s₂.1 -> s₁ = s₂ :=
begin 
  intro p, fapply sigma.sigma_eq, 
  exact p, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end  

end hott
