import hott.algebra.ring categorial_limits

universes u v w
hott_theory

namespace hott
open is_trunc hott.algebra category_theory 

namespace algebra

/- Bundled structure of commutative rings -/
@[hott] 
structure CommRing :=
(carrier : Type u) (struct : comm_ring carrier)

@[hott]
instance has_coe_CommRing : has_coe_to_sort CommRing.{u} :=
  ⟨Type u, CommRing.carrier⟩

attribute [instance] Ring.struct

@[hott]
structure monoid_hom (M N : Monoid.{u}) :=
  (to_fun : M -> N)
  (map_one : to_fun 1 = 1)
  (map_mul : ∀ a b : M, to_fun (a * b) = to_fun a * to_fun b)

infixr ` →* `:25 := monoid_hom

@[hott]
def monoid_hom_is_set (M N : Monoid) : is_set (M →* N) :=
  have set_eq_eq : ∀ (g h : M →* N) (p q : g = h), p = q, from
    begin intros g h p q, hinduction p, hinduction g, sorry end, 
  is_set.mk _ set_eq_eq 

end algebra

end hott
