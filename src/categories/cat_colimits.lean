import setalgebra categories.examples

universes v u v' u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.set hott.subset 
     hott.categories 

/- We introduce colimits of diagrams mapped to categories, by using cocones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace category_theory.colimits

structure cocone {J : Set.{v}} [precategory J] {C : Type u} 
  [precategory C] (F : J ⥤ C) :=
(X : C)
(π : F ⟹ (constant_functor J C X))

@[hott]
structure is_colimit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (t : cocone F) :=
(desc : Π (s : cocone F), t.X ⟶ s.X)
(fac  : ∀ (s : cocone F) (j : J), t.π.app j ≫ desc s = s.π.app j)
(uniq : ∀ (s : cocone F) (m : t.X ⟶ s.X) 
          (w : ∀ j : J, t.π.app j ≫ m = s.π.app j), m = desc s)

@[hott] 
def desc_itself_id {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} {t : cocone F} (l : is_colimit t) : l.desc t = 𝟙 t.X :=
have t_fac : ∀ j : J, t.π.app j ≫ 𝟙 t.X = t.π.app j, by intro j; hsimp,  
(l.uniq _ _ t_fac)⁻¹             

@[hott]
def colimit_cocone_point_iso {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} {s t : cocone F} (lₛ : is_colimit s) (lₜ : is_colimit t) : 
Σ i : t.X ≅ s.X, i.hom = lₜ.desc s :=
let st := lₜ.desc s, ts := lₛ.desc t in 
have s_fac : ∀ j : J, s.π.app j ≫ (ts ≫ st) = s.π.app j, from assume j,
  calc s.π.app j ≫ (ts ≫ st) = (s.π.app j ≫ ts) ≫ st : (precategory.assoc _ _ _)⁻¹
       ... = t.π.app j ≫ st : by rwr lₛ.fac t j
       ... = s.π.app j : by rwr lₜ.fac s j,
have t_fac : ∀ j : J, t.π.app j ≫ (st ≫ ts) = t.π.app j, from assume j, 
  calc t.π.app j ≫ (st ≫ ts) = (t.π.app j ≫ st) ≫ ts : (precategory.assoc _ _ _)⁻¹
       ... = s.π.app j ≫ ts : by rwr lₜ.fac s j 
       ... = t.π.app j : by rwr lₛ.fac t j,
have comp_s : ts ≫ st = 𝟙 s.X, from lₛ.uniq _ _ s_fac ⬝ desc_itself_id lₛ, 
have comp_t : st ≫ ts = 𝟙 t.X, from lₜ.uniq _ _ t_fac ⬝ desc_itself_id lₜ,
⟨iso.mk st ts comp_s comp_t, rfl⟩

/- `colimit_cocone F` contains a cocone over `F` together with the information that 
   it is a colimit. -/
@[hott]
structure colimit_cocone {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

/- `has_colimit F` represents the mere existence of a colimit for `F`. This allows
   to define it as a class with instances. -/ 
@[hott]   
class has_colimit {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  (F : J ⥤ C) :=
mk' :: (exists_colimit : ∥colimit_cocone F∥)

@[hott]
def has_colimit.mk {J : Set.{v}} [precategory J] {C : Type u} [precategory C] 
  {F : J ⥤ C} (d : colimit_cocone F) :=
has_colimit.mk' (tr d) 

/- If `C` is a category, the colimit cocone vertices of two instances of 
  `colimit_cocone F` are equal since they are determined up to isomorphism. Then 
   the "legs" of the cocones and the descendants of the universal property are 
   determined up to composition with the automorphism associated to this 
   equality of colimit cocone vertices, and colimit cocones are equal. 
   
   Thus, we can produce a `colimit_cocone F` from `has_colimit F`. -/
@[hott]
def colimit_cocone_is_unique {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : ∀ lc₁ lc₂ : colimit_cocone F, lc₁ = lc₂ :=
begin
  intros lc₁ lc₂, 
  hinduction lc₁ with cocone₁ is_colimit₁, hinduction lc₂ with cocone₂ is_colimit₂,
  have cocone_id : cocone₁ = cocone₂, from 
  begin
    hinduction cocone₁ with X₁ π₁, hinduction cocone₂ with X₂ π₂,  
    let lcp_iso := colimit_cocone_point_iso is_colimit₁ is_colimit₂,
    fapply apd011 cocone.mk,
    { exact idtoiso⁻¹ᶠ (inv_iso lcp_iso.1) },
    { hinduction π₁ with app₁ nat₁, hinduction π₂ with app₂ nat₂, 
      fapply apdo0111 (λ c : C, @nat_trans.mk _ _ _ _ F (constant_functor ↥J C c)),
      { apply pathover_of_tr_eq, apply eq_of_homotopy, 
        intro j, rwr tr_fn_tr_eval,
        change idtoiso⁻¹ᶠ (inv_iso lcp_iso.1) ▸[λ X : C, F.obj j ⟶ X] app₁ j = app₂ j, 
        rwr iso_hom_tr_comp' (inv_iso lcp_iso.1) (app₁ j), apply inverse, 
        apply iso_move_rl,
        exact (is_colimit₂.fac _ j) },
      { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros c c' f, 
        apply is_set.elim } }
  end,
  have is_colimit_id : is_colimit₁ =[cocone_id] is_colimit₂, from 
  begin 
    hinduction cocone_id,
    hinduction is_colimit₁ with desc₁ fac₁ uniq₁,
    hinduction is_colimit₂ with desc₂ fac₂ uniq₂, 
    fapply apdo01111 (@is_colimit.mk _ _ _ _ _),
    { apply pathover_of_tr_eq, hsimp, apply eq_of_homotopy, intro s,
      apply uniq₂, exact fac₁ s },
    { apply pathover_of_tr_eq, apply eq_of_homotopy2, intros s j, 
        apply is_set.elim },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros s m id, 
        apply is_set.elim }
  end,
  fapply apd011 colimit_cocone.mk,
  { exact cocone_id },
  { exact is_colimit_id }
end  

@[hott, instance]
def colimit_cocone_is_prop {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) : is_trunc -1 (colimit_cocone F) :=
is_prop.mk (colimit_cocone_is_unique F)

@[hott]
def get_colimit_cocone {J : Set.{v}} [precategory J] {C : Type u} [category C] 
  (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
untrunc_of_is_trunc (has_colimit.exists_colimit F)  

@[hott]
def colimit.cocone {J : Set.{v}} [precategory J] {C : Type u} [category C]
  (F : J ⥤ C) [has_colimit F] : cocone F := (get_colimit_cocone F).cocone

@[hott]
def colimit {J : Set.{v}} [precategory J] {C : Type u} [category C]
  (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X

@[hott]
class has_colimits_of_shape (J : Set) [precategory J] (C : Type u) 
  [category C] :=
  (has_colimit : Π F : J ⥤ C, has_colimit F)

@[hott, priority 100]
instance has_colimit_of_has_colimits_of_shape
  {J : Set} [precategory J] (C : Type u) [category C] 
  [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
has_colimits_of_shape.has_colimit F

/- The category of sets has all colimits. 

   The limit cocone is constructed as the quotient of the disjoint union of the sets in the 
   cocone base by the compatibility conditions of the indexing category. We define this 
   relation separately, for use later on.
   
   Note that the limit cocone vertex may be the empty set - then all cones over the functor `F`
   are empty because they cannot factorize through the empty set. -/

end category_theory.colimits

end hott