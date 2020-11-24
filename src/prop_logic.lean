import hott.init hott.types.trunc

universes u v w
hott_theory

set_option pp.universes true
set_option pp.implicit true

namespace hott
open is_trunc trunc equiv is_equiv

@[hott]
inductive true : Type u
| intro : true

@[hott]
lemma eq_true : forall t₁ t₂ : true, t₁ = t₂ :=
begin 
  intros, 
  induction t₁, 
  induction t₂,
  exact (refl true.intro)
end 

@[hott]
lemma is_prop_true : is_prop true :=
  is_prop.mk eq_true 

@[hott]
def True : Prop :=
  Prop.mk true is_prop_true  

@[hott]
inductive false : Type u

end hott