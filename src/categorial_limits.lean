import setalgebra category_theory

universes v u v' u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.set hott.subset 
     hott.category_theory 

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
  {F : J ⥤ C} {s t : cone F} (lₛ : is_limit s) (lₜ : is_limit t) : 
Σ i : s.X ≅ t.X, i.hom = lₜ.lift s :=
let st := lₜ.lift s, ts := lₛ.lift t in 
have s_fac : ∀ j : J, (st ≫ ts) ≫ s.π.app j = s.π.app j, from assume j,
  calc (st ≫ ts) ≫ s.π.app j = st ≫ (ts ≫ s.π.app j) : precategory.assoc _ _ _
       ... = st ≫ t.π.app j : by rwr lₛ.fac t j
       ... = s.π.app j : by rwr lₜ.fac s j,
have t_fac : ∀ j : J, (ts ≫ st) ≫ t.π.app j = t.π.app j, from assume j, 
  calc (ts ≫ st) ≫ t.π.app j = ts ≫ (st ≫ t.π.app j) : precategory.assoc _ _ _
       ... = ts ≫ s.π.app j : by rwr lₜ.fac s j 
       ... = t.π.app j : by rwr lₛ.fac t j,
have comp_s : st ≫ ts = 𝟙 s.X, from lₛ.uniq _ _ s_fac ⬝ lift_itself_id lₛ, 
have comp_t : ts ≫ st = 𝟙 t.X, from lₜ.uniq _ _ t_fac ⬝ lift_itself_id lₜ,
⟨iso.mk st ts comp_t comp_s, rfl⟩

/- `limit_cone F` contains a cone over `F` together with the information that 
   it is a limit. -/
@[hott]
structure limit_cone {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

/- `has_limit F` represents the mere existence of a limit for `F`. This allows
   to define it as a class with instances. -/ 
@[hott]   
class has_limit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
mk' :: (exists_limit : ∥limit_cone F∥)

@[hott]
def has_limit.mk {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (d : limit_cone F) :=
has_limit.mk' (tr d)  

/- If `C` is a category, the limit cone points of two instances of 
  `limit_cone F` are equal since they are determined up to isomorphism. Then 
   the "legs" of the cones and the lifts of the universal property are 
   determined up to composition with the automorphism associated to this 
   equality of limit cone points, and limit cones are equal. 
   
   Thus, we can produce a `limit_cone F` from `has_limit F`. -/
@[hott]
def limit_cone_is_unique {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : ∀ lc₁ lc₂ : limit_cone F, lc₁ = lc₂ :=
begin
  intros lc₁ lc₂, 
  hinduction lc₁ with cone₁ is_limit₁, hinduction lc₂ with cone₂ is_limit₂,
  have cone_id : cone₁ = cone₂, from 
  begin
    hinduction cone₁ with X₁ π₁, hinduction cone₂ with X₂ π₂,  
    let lcp_iso := limit_cone_point_iso is_limit₁ is_limit₂,
    fapply apd011 cone.mk,
    { exact idtoiso⁻¹ᶠ lcp_iso.1 },
    { hinduction π₁ with app₁ nat₁, hinduction π₂ with app₂ nat₂, 
      fapply apdo0111 (λ c : C, @nat_trans.mk _ _ _ _ (constant_functor ↥J C c) F),
      { apply pathover_of_tr_eq, apply eq_of_homotopy, 
        intro j, rwr tr_fn_tr_eval,
        change idtoiso⁻¹ᶠ lcp_iso.1 ▸[λ X : C, X ⟶ F.obj j] app₁ j = app₂ j, 
        rwr iso_hom_tr_comp lcp_iso.1 (app₁ j), apply inverse, 
        apply iso_move_lr,
        exact (ap (λ h : X₁ ⟶ X₂, h ≫ app₂ j) lcp_iso.2) ⬝ 
              (is_limit₂.fac _ j)},
      { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros c c' f, 
        apply is_set.elim } }
  end,
  have is_limit_id : is_limit₁ =[cone_id] is_limit₂, from 
  begin 
    hinduction cone_id,
    hinduction is_limit₁ with lift₁ fac₁ uniq₁,
    hinduction is_limit₂ with lift₂ fac₂ uniq₂, 
    fapply apdo01111 (@is_limit.mk _ _ _ _ _),
    { apply pathover_of_tr_eq, hsimp, apply eq_of_homotopy, intro s,
      apply uniq₂, exact fac₁ s },
    { apply pathover_of_tr_eq, apply eq_of_homotopy2, intros s j, 
        apply is_set.elim },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros s m id, 
        apply is_set.elim }
  end,
  fapply apd011 limit_cone.mk,
  { exact cone_id },
  { exact is_limit_id }
end    

@[hott, instance]
def limit_cone_is_prop {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : is_trunc -1 (limit_cone F) :=
is_prop.mk (limit_cone_is_unique F)

@[hott]
def get_limit_cone {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) [has_limit F] : limit_cone F :=
untrunc_of_is_trunc (has_limit.exists_limit F)  

@[hott]
class has_limits_of_shape (J : Set.{v}) [precategory J] (C : Type u) 
  [category C] :=
  (has_limit : Π F : J ⥤ C, has_limit F)

abbreviation has_products {C : Type u} [category C] := 
  Π (J : Set.{v}), has_limits_of_shape (discrete J) C

/- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
@[hott, hsimp]
def parallel_pair_obj {C : Type u} [category_theory.category C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair.{u} -> C :=
λ s, match s with
     | walking_parallel_pair.up := a
     | walking_parallel_pair.down := b
     end    

@[hott, hsimp]
def parallel_pair_map {C : Type u} [category_theory.category C] {a b : C} 
  (f g : a ⟶ b) : Π {s t : walking_parallel_pair.{u}}, 
  (s ⟶ t) -> (parallel_pair_obj f g s ⟶ parallel_pair_obj f g t) :=
assume s t h, 
begin
  hinduction s, 
  { hinduction t,
    { exact 𝟙 a },
    { hinduction h,
      { exact f },
      { exact g } } },
  { hinduction t,
    { hinduction h },
    { exact 𝟙 b } }
end 

@[hott, hsimp]
def parallel_pair_map_id {C : Type u} [category_theory.category C] {a b : C} 
  (f g : a ⟶ b) : ∀ s : walking_parallel_pair.{u}, 
  parallel_pair_map f g (𝟙 s) = 𝟙 (parallel_pair_obj f g s) :=
by intro s; hinduction s; hsimp; hsimp  

@[hott, hsimp]
def parallel_pair_map_id' {C : Type u} [category_theory.category C] {a b : C} 
  (f g : a ⟶ b) : ∀ (s : walking_parallel_pair.{u}) (h : s ⟶ s), 
  parallel_pair_map f g h = 𝟙 (parallel_pair_obj f g s) :=
by intros s h; hinduction s; hsimp; hsimp  

@[hott, hsimp]
def parallel_pair_map_comp {C : Type u} [category_theory.category C] 
  {a b : C} (f g : a ⟶ b) : ∀ {s t u : walking_parallel_pair.{u}} 
  (h : s ⟶ t) (i : t ⟶ u), parallel_pair_map f g (h ≫ i) = 
                  (parallel_pair_map f g h) ≫ (parallel_pair_map f g i) :=
assume s t u h i,
begin
  hinduction s,
  { hinduction t,
    { hsimp },
    { hinduction u,
      { hinduction i },
      { rwr wpp_ci, hsimp } } },
  { hinduction t,
    { induction h },
    { hsimp } }
end  

@[hott]
def parallel_pair {C : Type u} [category_theory.category C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair.{u} ⥤ C :=
category_theory.functor.mk (parallel_pair_obj f g) 
                           (@parallel_pair_map _ _ _ _ f g) 
                           (parallel_pair_map_id f g) 
                           (@parallel_pair_map_comp _ _ _ _ f g)   

end category_theory.limits

end hott