import setalgebra categories.examples

universes v u v' u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.set hott.subset 
     hott.categories 

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
def limit.cone {J : Set.{v}} [precategory J] {C : Type u} [category C]
  (F : J ⥤ C) [has_limit F] : cone F := (get_limit_cone F).cone

@[hott]
def limit {J : Set.{v}} [precategory J] {C : Type u} [category C]
  (F : J ⥤ C) [has_limit F] := (limit.cone F).X

@[hott]
class has_limits_of_shape (J : Set) [precategory J] (C : Type u) 
  [category C] :=
  (has_limit : Π F : J ⥤ C, has_limit F)

@[hott, priority 100]
instance has_limit_of_has_limits_of_shape
  {J : Set} [precategory J] (C : Type u) [category C] 
  [H : has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
has_limits_of_shape.has_limit F

@[hott]
class has_limits (C : Type (u+1)) [category.{u} C] :=
  (has_limit_of_shape : Π (J : Set) [precategory J], has_limits_of_shape J C )  

@[hott]
abbreviation has_product {C : Type (u+1)} [category C] {J : Set.{u}} 
  (f : J -> C) := has_limit (discrete.functor f) 

@[hott]
abbreviation pi_obj {C : Type (u+1)} [category.{u} C] {J : Set.{u}} (f : J → C) 
  [has_product f] := limit (discrete.functor f)

notation `∏ ` f:20 := pi_obj f

@[hott]
class has_products (C : Type (u+1)) [category.{u} C] := 
  (has_limit_of_shape : Π J : Set.{u}, has_limits_of_shape (discrete J) C)

@[hott, priority 100]
instance has_limits_of_shape_of_has_products 
  {J : Set} (C : Type (u+1)) [category.{u} C] [has_products C] :
  has_limits_of_shape (discrete J) C :=
has_products.has_limit_of_shape C J

@[hott, instance, priority 100]
def has_product_of_has_products {C : Type (u+1)} [category.{u} C] 
  [has_products C] {J : Set.{u}} (f : J -> C) : has_product f :=
@has_limits_of_shape.has_limit _ _ _ _ 
       (has_products.has_limit_of_shape C J) (discrete.functor f)

@[hott, instance]
def has_product_of_has_limits_of_shape {C : Type (u+1)} [category.{v} C] 
  {J : Set.{u}} [has_limits_of_shape (discrete J) C] (f : J -> C) : 
  has_product f :=
has_limits_of_shape.has_limit (discrete.functor f) 

@[hott, instance]
def has_products_of_has_limits (C : Type (u+1)) [category.{u} C] [c : has_limits C] : 
  has_products C :=
has_products.mk (λ J, @has_limits.has_limit_of_shape C _ c (discrete J) _)

/-- A fan over `f : J → C` consists of a collection of maps from an object `P`
    to every `f j`. This is enough to determine a cone which factorizes through    
    the product. -/
@[hott]    
abbreviation fan {J : Set} {C : Type u} [category C] (f : J → C) := 
  cone (discrete.functor f)

@[hott, hsimp]
def fan.mk {J : Set} (C : Type u) [category C] {f : J → C} {P : C} 
  (p : Π j, P ⟶ f j) : fan f :=
cone.mk P (discrete.nat_trans _ _ p)

@[hott, hsimp] 
def pi.lift {J : Set} (C : Type (u+1)) [category.{u} C] {f : J → C} [has_product f]
  {P : C} (p : Π j, P ⟶ f j) : P ⟶ ∏ f :=
(get_limit_cone (discrete.functor f)).is_limit.lift (fan.mk _ p)  

@[hott, hsimp] 
def pi.π {J : Set} {C : Type (u+1)} [category.{u} C] (f : J → C) [has_product f] 
  (j : J) : ∏ f ⟶ f j :=
(limit.cone (discrete.functor f)).π.app j 

@[hott]
def pi.hom_is_lift {J : Set} (C : Type (u+1)) [category.{u} C] {f : J → C} 
  [has_product f] {P : C} (h : P ⟶ ∏ f) : 
  h = pi.lift C (λ j : J, h ≫ (pi.π _ j)) :=
let p := λ j : J, h ≫ (pi.π f j),
    c := fan.mk _ p,
    lc := get_limit_cone (discrete.functor f) in     
begin 
  change h = lc.is_limit.lift c, 
  apply is_limit.uniq lc.is_limit c h, 
  intro j, exact rfl, 
end  

@[hott]
def pi.lift_π_eq {J : Set} (C : Type (u+1)) [category.{u} C] {f : J → C} 
  [has_product f] {P : C} (p : Π j : J, P ⟶ f j) : 
  ∀ j : J, pi.lift C p ≫ pi.π _ j = p j :=
assume j, by apply is_limit.fac  

/- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
@[hott, hsimp]
def parallel_pair_obj {C : Type u} [category C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair.{u} -> C :=
λ s, match s with
     | wp_pair.up := a
     | wp_pair.down := b
     end    

@[hott, hsimp]
def parallel_pair_map {C : Type u} [category C] {a b : C} 
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
def parallel_pair_map_id {C : Type u} [category C] {a b : C} 
  (f g : a ⟶ b) : ∀ s : walking_parallel_pair.{u}, 
  parallel_pair_map f g (𝟙 s) = 𝟙 (parallel_pair_obj f g s) :=
by intro s; hinduction s; hsimp; hsimp  

@[hott, hsimp]
def parallel_pair_map_id' {C : Type u} [category C] {a b : C} 
  (f g : a ⟶ b) : ∀ (s : walking_parallel_pair.{u}) (h : s ⟶ s), 
  parallel_pair_map f g h = 𝟙 (parallel_pair_obj f g s) :=
by intros s h; hinduction s; hsimp; hsimp  

@[hott, hsimp]
def parallel_pair_map_comp {C : Type u} [category C] 
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
def parallel_pair {C : Type u} [category C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair.{u} ⥤ C :=
categories.functor.mk (parallel_pair_obj f g) 
                           (@parallel_pair_map _ _ _ _ f g) 
                           (parallel_pair_map_id f g) 
                           (@parallel_pair_map_comp _ _ _ _ f g)   

@[hott]
abbreviation fork {C : Type u} [category C] {a b : C} 
  (f g : a ⟶ b) := cone (parallel_pair f g) 

@[hott]
def fork.of_i {C : Type u} [category C] {a b c : C} 
  (f g : a ⟶ b) (i : c ⟶ a) (w : i ≫ f = i ≫ g) : fork f g :=
have π : constant_functor ↥walking_parallel_pair C c ⟹ parallel_pair f g, from
  let app :=  @wp_pair.rec (λ x, c ⟶ (parallel_pair f g).obj x) i (i ≫ f) in
  have naturality : ∀ (x x' : walking_parallel_pair) (h : x ⟶ x'), 
          ((constant_functor ↥walking_parallel_pair C c).map h) ≫ (app x') = 
           (app x) ≫ ((parallel_pair f g).map h), from 
  begin
    intros x x' h, 
    hinduction x,
    { hinduction x',
      { hinduction h, hsimp },
      { hinduction h, 
        { hsimp, refl },
        { hsimp, exact w } } },  
    { hinduction x', 
      { hinduction h },
      { hinduction h, hsimp } }
  end,           
  nat_trans.mk app naturality,   
cone.mk c π 

/- The category of sets has all limits. 

   The limit cone is constructed as the sections of the functor map satisfying the 
   compatibility conditions of the indexing category. We define this predicate separately, 
   for use later on.
   
   Note that the limit cone vertex may be the empty set - then all cones over the functor `F`
   are empty because they cannot factorize through the empty set. -/
@[hott]
def set_limit_pred {J : Set.{v}} [precategory.{v} J] (F : J ⥤ Set.{v}) : 
  Setpred (Sections (λ j : J, F.obj j)) :=
λ u, to_Prop (∀ {j k : J} (f : j ⟶ k), F.map f (u j) = u k)  

@[hott, reducible]
def set_cone {J : Set.{v}} [precategory.{v} J] (F : J ⥤ Set.{v}) : cone F :=
begin
  fapply cone.mk,
  /- The limit cone vertex set -/
  { exact ↥{ u ∈ (Sections F.obj) | set_limit_pred F u } },
  { fapply nat_trans.mk, 
    /- the leg maps of the limit cone -/
    { intro j, exact λ u, u.1 j },
    /- compatibility of the leg maps -/
    { intros j k f, hsimp, 
      fapply eq_of_homotopy, intro u, hsimp, 
      change u.1 k = F.map f (u.1 j), rwr u.2 } }
end  

@[hott, reducible]
def set_cone_is_limit {J : Set.{v}} [precategory.{v} J] (F : J ⥤ Set.{v}) :
  is_limit (set_cone F) :=
begin 
  fapply is_limit.mk,
  /- the lift from the limit cone to another cone-/ 
  { intro s, intro x, fapply sigma.mk, 
    { intro j, exact s.π.app j x },
    { intros j k f, hsimp,  
      exact (homotopy_of_eq (s.π.naturality f) x)⁻¹ } },
  /- factorising the lift with limit cone legs -/    
  { intros s j, hsimp, apply eq_of_homotopy, 
    intro x, refl },
  /- uniqueness of lift -/  
  { intros s m lift_m, hsimp, apply eq_of_homotopy,
    intro x, hsimp, fapply sigma.sigma_eq, 
    { hsimp, apply eq_of_homotopy, intro j, hsimp, rwr <- lift_m j },
    { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros j k f, 
        apply is_set.elim } }  
end

@[hott, reducible]
def set_limit_cone {J : Set.{v}} [precategory.{v} J] (F : J ⥤ Set.{v}) : limit_cone F :=
  limit_cone.mk (set_cone F) (set_cone_is_limit F)

@[hott, instance]
def set_has_limit {J : Set.{v}} [precategory.{v} J] (F : J ⥤ Set.{v}) : has_limit F :=
  has_limit.mk (set_limit_cone F)

@[hott, instance]
def set_has_limits_of_shape {J : Set.{v}} [precategory.{v} J] : has_limits_of_shape J Set.{v} :=
  has_limits_of_shape.mk (λ F, set_has_limit F)     

/- A criterion for a category of standard structures over a category with limits to have limits:
   - The limit cone of the underlying functor of a shape carries a structure.
   - The leg morphisms of this limit cone respect the structures.
   - The lift morphisms to this limit cone respect the structures. 
   
   We first need to construct the underlying cone of a cone in the category of structures. -/
@[hott, reducible]
def str_cone_to_cone {J : Set.{v}} [precategory.{v} J] {C : Type (v+1)} [category.{v} C] 
  {std_str : std_structure_on C} {F : J ⥤ (std_structure std_str)} (s : cone F) :
  cone (forget F) :=
begin 
  fapply cone.mk, 
  { exact s.X.1 },  -- vertex
  { fapply nat_trans.mk,
    { intro j, exact (s.π.app j).1 },  --transformation of objects
    { intros j k f, hsimp, 
      change (s.π.app k).1 = (s.π.app j).1 ≫ (F.map f).1, rwr <- comp_hom_std_C _ _,
      rwr <- ap sigma.fst (s.π.naturality f), hsimp } }  --naturality
end    

/- We define the the structure data of a limit cone for all limit cones of the underlying
   category at once, because we can change then easily to the best suited construction. -/
@[hott]
structure limit_cone_str_data {J : Set.{v}} [precategory.{v} J] {C : Type (v+1)} 
  [category.{v} C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  {F : J ⥤ (std_structure std_str)} (lc : limit_cone (forget F)) :=
(lc_str : std_str.P (lc.cone.X)) 
(lc_legs_H : Π (j : J), std_str.H lc_str ((F.obj j).str) (lc.cone.π.app j))
(lift_H : Π (s : cone F), std_str.H s.X.str lc_str (lc.is_limit.lift (str_cone_to_cone s)))

@[hott]
def str_limit_cone {J : Set.{v}} [precategory.{v} J] {C : Type (v+1)} 
  [category.{v} C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  {F : J ⥤ (std_structure std_str)} (lc : limit_cone (forget F))
  (lcd : limit_cone_str_data lc) : limit_cone F :=
begin 
  fapply limit_cone.mk, 
  { fapply cone.mk, -- the limit cone 
    { exact std_structure.mk lc.cone.X lcd.lc_str},
    { fapply nat_trans.mk, 
      { intro j, 
        exact ⟨lc.cone.π.app j, lcd.lc_legs_H j⟩ },
      { intros j k f, apply hom_eq_C_std, rwr comp_hom_std_C,  
        exact lc.cone.π.naturality f } } },
  { fapply is_limit.mk, -- the limit cone is a limit
    { intro s, 
      exact ⟨lc.is_limit.lift (str_cone_to_cone s), lcd.lift_H s⟩ },
    { intros s j, apply hom_eq_C_std, rwr comp_hom_std_C, hsimp, 
      exact lc.is_limit.fac (str_cone_to_cone s) j },
    { intros s m fac_m, apply hom_eq_C_std, hsimp, 
      have fac_m1 : ∀ j : J, m.1 ≫ (lc.cone.π.app j) = 
                                                   (str_cone_to_cone s).π.app j, from 
        assume j, 
        calc m.1 ≫ (lc.cone.π.app j) = (s.π.app j).1 : ap sigma.fst (fac_m j)
             ... = (str_cone_to_cone s).π.app j : rfl,
      exact lc.is_limit.uniq (str_cone_to_cone s) m.1 fac_m1 } }
end                

@[hott]
def str_has_limit {J : Set.{v}} [precategory.{v} J] {C : Type (v+1)} 
  [category.{v} C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  (F : J ⥤ (std_structure std_str)) 
  (lcd : limit_cone_str_data (get_limit_cone (forget F))) : has_limit F :=
has_limit.mk (str_limit_cone (get_limit_cone (forget F)) lcd)                                           

@[hott, instance]
def std_structure_has_limits_of_shape {J : Set.{v}} [precategory.{v} J] {C : Type (v+1)} 
  [category.{v} C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  (lcd_F : Π F : J ⥤ (std_structure std_str), limit_cone_str_data (get_limit_cone (forget F))): 
  has_limits_of_shape J (std_structure std_str) :=
has_limits_of_shape.mk (λ F, str_has_limit F (lcd_F F))

end category_theory.limits

end hott