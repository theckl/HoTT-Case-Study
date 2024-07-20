import hott.algebra.group

universes u u' v w
hott_theory

namespace hott
open is_trunc hott.algebra 

structure mul_Hom (A : Type _) (B : Type _) [has_mul A] [has_mul B] :=
  (to_fun : A -> B)
  (map_mul : ∀ a₁ a₂ : A, to_fun (a₁ * a₂) = (to_fun a₁) * (to_fun a₂)) 

structure semigroup_Hom (A : Type _) (B : Type _) [hott.algebra.semigroup A] 
  [hott.algebra.semigroup B] :=
(to_mul_Hom : mul_Hom A B)

structure monoid_Hom (A : Type _) (B : Type _) [hott.algebra.monoid A] 
  [hott.algebra.monoid B] :=
(to_semigroup_Hom : semigroup_Hom A B)
(map_one : to_semigroup_Hom.to_mul_Hom.to_fun 1 = 1)

structure comm_monoid_Hom (A : Type _) (B : Type _) 
  [hott.algebra.comm_monoid A] [hott.algebra.comm_monoid B] :=
(to_monoid_hom : monoid_Hom A B)

end hott