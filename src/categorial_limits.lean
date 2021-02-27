import setalgebra category_theory

universes v u v' u' w
hott_theory

namespace hott
open hott.is_trunc hott.trunc hott.set hott.subset hott.category_theory

/- We introduce limits of diagrams mapped to categories, by using cones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace category_theory.limits

structure cone {J : Set.{v}} [precategory J] {C : Type u} 
  [precategory C] (F : J ⥤ C) :=
(X : C)
(π : (constant_functor J C X) ⟹ F)

@[hott]
structure is_limit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (t : cone F) :=
(lift : Π (s : cone F), s.X ⟶ t.X)
(fac  : ∀ (s : cone F) (j : J), lift s ≫ t.π.app j = s.π.app j)
(uniq : ∀ (s : cone F) (m : s.X ⟶ t.X) 
          (w : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s)

@[hott] 
def lift_itself_id {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} {t : cone F} (l : is_limit t) : l.lift t = 𝟙 t.X :=
have t_fac : ∀ j : J, 𝟙 t.X ≫ t.π.app j = t.π.app j, by intro j; hsimp,  
(l.uniq _ _ t_fac)⁻¹             

@[hott]
def limit_cone_point_iso {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} {s t : cone F} (lₛ : is_limit s) (lₜ : is_limit t) : s.X ≅ t.X :=
let st := lₜ.lift s, ts := lₛ.lift t in 
have s_fac : ∀ j : J, (st ≫ ts) ≫ s.π.app j = s.π.app j, from assume j,
  sorry,
have t_fac : ∀ j : J, (ts ≫ st) ≫ t.π.app j = t.π.app j, from assume j, 
  sorry,
have comp_s : st ≫ ts = 𝟙 s.X, from lₛ.uniq _ _ s_fac ⬝ lift_itself_id lₛ, 
have comp_t : ts ≫ st = 𝟙 t.X, from lₜ.uniq _ _ t_fac ⬝ lift_itself_id lₜ,
iso.mk st ts comp_t comp_s

/- `limit_cone F` contains a cone over `F` together with the information that 
   it is a limit. -/
@[hott]
structure limit_cone {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

/- `has_limit F` represents the mere existence of a limit for `F`. This allows
   to define as a class with instances. However, if `C` is a category, 
   `limit_cone F` is a (-1)-Type since limits are determined up to isomorphism,
   so we can extract a limit cone from `has_limit`. -/
@[hott]   
class has_limit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
mk' :: (exists_limit : ∥limit_cone F∥)

@[hott]
def has_limit.mk {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (d : limit_cone F) :=
has_limit.mk' (tr d)  

@[hott]
def limit_cone_is_unique {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : ∀ lc₁ lc₂ : limit_cone F, lc₁ = lc₂ :=
begin
  intros lc₁ lc₂, 
  hinduction lc₁ with cone₁ is_limit₁, 
  hinduction lc₂ with cone₂ is_limit₂,
  have cone_id : cone₁ = cone₂, from 
    begin 
      hinduction cone₁ with X₁ π₁,
      hinduction cone₂ with X₂ π₂,
      have cone_pt_id : X₁ = X₂, from sorry,
      apply apd011 cone.mk cone_pt_id,
      sorry
    end,
  apply apd011 limit_cone.mk cone_id,
  sorry
end    

@[hott, instance]
def limit_cone_is_prop {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : is_trunc -1 (limit_cone F) :=
is_prop.mk (limit_cone_is_unique F)

@[hott]
def get_limit_cone {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) [has_limit F] : limit_cone F :=
untrunc_of_is_trunc (has_limit.exists_limit F)  

end category_theory.limits

end hott