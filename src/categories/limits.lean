import sets.algebra categories.examples categories.diagrams

universes v v' u u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.set hott.subset 
     hott.categories 

/- We introduce limits of diagrams mapped to categories, by using cones to 
   pick the universal object and encode the universal property.

   As far as possible we copy the mathlib-code in [category_theory.limits]. -/

namespace categories.limits

set_option pp.universes false

@[hott]
structure cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [precategory.{v} C] (F : J ⥤ C) :=
(X : C)
(π : (constant_functor J C X) ⟹ F)

@[hott]
def cone.fac {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [precategory.{v} C] {F : J ⥤ C} (s : cone F) : 
  ∀ {j k : J} (f : j ⟶ k), s.π.app j ≫ F.map f = s.π.app k :=
begin intros j k f, rwr <- s.π.naturality f, hsimp end   

@[hott]
structure is_limit {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [precategory.{v} C] 
  {F : J ⥤ C} (t : cone F) :=
(lift : Π (s : cone F), s.X ⟶ t.X)
(fac  : ∀ (s : cone F) (j : J), lift s ≫ t.π.app j = s.π.app j)
(uniq : ∀ (s : cone F) (m : s.X ⟶ t.X) 
          (w : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s)

@[hott] 
def lift_itself_id {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [precategory.{v} C] 
  {F : J ⥤ C} {t : cone F} (l : is_limit t) : l.lift t = 𝟙 t.X :=
have t_fac : ∀ j : J, 𝟙 t.X ≫ t.π.app j = t.π.app j, by intro j; hsimp,  
(l.uniq _ _ t_fac)⁻¹             

@[hott]
def limit_cone_point_iso {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [precategory.{v} C] 
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
structure limit_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [precategory.{v} C] 
  (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

/- `has_limit F` represents the mere existence of a limit for `F`. This allows
   to define it as a class with instances. -/ 
@[hott]   
class has_limit {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [precategory.{v} C] 
  (F : J ⥤ C) :=
mk' :: (exists_limit : ∥limit_cone F∥)

@[hott]
def has_limit.mk {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [precategory.{v} C] 
  {F : J ⥤ C} (d : limit_cone F) :=
has_limit.mk' (tr d)  

/- If `C` is a category, the limit cone points of two instances of 
  `limit_cone F` are equal since they are determined up to isomorphism. Then 
   the "legs" of the cones and the lifts of the universal property are 
   determined up to composition with the automorphism associated to this 
   equality of limit cone points, and limit cones are equal. 
   
   Thus, we can produce a `limit_cone F` from `has_limit F`. -/
@[hott]
def limit_cone_is_unique {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
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
def limit_cone_is_prop {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  (F : J ⥤ C) : is_trunc -1 (limit_cone F) :=
is_prop.mk (limit_cone_is_unique F)

@[hott]
def get_limit_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  (F : J ⥤ C) [has_limit F] : limit_cone F :=
untrunc_of_is_trunc (has_limit.exists_limit F)  

@[hott]
def limit.cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C]
  (F : J ⥤ C) [has_limit F] : cone F := (get_limit_cone F).cone

@[hott]
def limit {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C]
  (F : J ⥤ C) [has_limit F] := (limit.cone F).X

@[hott]
def limit_leg {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C]
  (F : J ⥤ C) (j : J) [has_limit F] : limit F ⟶ F.obj j := (limit.cone F).π.app j 

@[hott]
class has_limits_of_shape (J : Set.{u'}) [precategory.{v'} J] (C : Type u) [category.{v} C] :=
  (has_limit : Π F : J ⥤ C, has_limit F)

@[hott, priority 100]
instance has_limit_of_has_limits_of_shape
  {J : Set.{u'}} [precategory.{v'} J] (C : Type u) [category.{v} C] 
  [has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
has_limits_of_shape.has_limit F

@[hott]
class has_limits (C : Type u) [category.{v} C] :=
  (has_limit_of_shape : Π (J : Set.{u'}) [precategory.{v'} J], has_limits_of_shape J C )  

@[hott]
class has_product {C : Type u} [category.{v} C] {J : Set.{u'}} (f : J -> C) := 
  (has_limit : has_limit (discrete.functor f)) 

@[hott, priority 100]
instance has_limit_of_has_product {C : Type u} [category.{v} C] {J : Set.{u'}} (f : J -> C)
  [has_product f] : has_limit (discrete.functor f) := 
has_product.has_limit f  

@[hott]
abbreviation pi_obj {C : Type u} [category.{v} C] {J : Set.{u'}} (f : J → C) [has_product f] := 
  limit (discrete.functor f)

notation `∏ ` f:20 := pi_obj f

@[hott]
class has_products (C : Type u) [category.{v} C] := 
  (has_limit_of_shape : Π J : Set.{u'}, has_limits_of_shape (discrete J) C)

@[hott, instance, priority 100]
def has_limits_of_shape_of_has_products 
  (J : Set.{u'}) (C : Type u) [category.{v} C] [has_products.{v u u'} C] :
  has_limits_of_shape (discrete J) C :=
has_products.has_limit_of_shape C J

@[hott]
instance has_product_of_has_products {C : Type u} [category.{v} C] 
  [has_products C] {J : Set.{u'}} (f : J -> C) : has_product f :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_products.has_limit_of_shape C J) (discrete.functor f)⟩

@[hott, instance]
def has_product_of_has_limits_of_shape {C : Type u} [category.{v} C] 
  {J : Set.{u'}} [has_limits_of_shape (discrete J) C] (f : J -> C) : 
  has_product f :=
⟨has_limits_of_shape.has_limit (discrete.functor f)⟩ 

@[hott, instance]
def has_products_of_has_limits (C : Type u) [category.{v} C] [c : has_limits C] : 
  has_products C :=
has_products.mk (λ J, @has_limits.has_limit_of_shape C _ c (discrete J) _)

/-- A fan over `f : J → C` consists of a collection of maps from an object `P`
    to every `f j`. This is enough to determine a cone which factorizes through    
    the product. -/
@[hott]    
abbreviation fan {J : Set.{u'}} {C : Type u} [category.{v} C] (f : J → C) := 
  cone (discrete.functor f)

@[hott, hsimp]
def fan.mk {J : Set.{u'}} (C : Type u) [category.{v} C] {f : J → C} {P : C} 
  (p : Π j, P ⟶ f j) : fan f :=
cone.mk P (discrete.nat_trans p)

@[hott, hsimp] 
def pi.lift {J : Set.{u'}} {C : Type u} [category.{v} C] {f : J → C} [has_product f]
  {P : C} (p : Π j, P ⟶ f j) : P ⟶ ∏ f :=
(get_limit_cone (discrete.functor f)).is_limit.lift (fan.mk _ p)  

@[hott, hsimp] 
def pi.π {J : Set.{u'}} {C : Type u} [category.{v} C] (f : J → C) [has_product f] 
  (j : J) : ∏ f ⟶ f j :=
(limit.cone (discrete.functor f)).π.app j 

@[hott]
def pi.hom_is_lift {J : Set.{u'}} {C : Type u} [category.{v} C] {f : J → C} 
  [has_product f] {P : C} (h : P ⟶ ∏ f) : 
  h = pi.lift (λ j : J, h ≫ (pi.π _ j)) :=
let p := λ j : J, h ≫ (pi.π f j),
    c := fan.mk _ p,
    lc := get_limit_cone (discrete.functor f) in     
begin 
  change h = lc.is_limit.lift c, 
  apply is_limit.uniq lc.is_limit c h, 
  intro j, exact rfl, 
end  

@[hott]
def pi.lift_π_eq {J : Set.{u'}} (C : Type u) [category.{v} C] {f : J → C} 
  [has_product f] {P : C} (p : Π j : J, P ⟶ f j) : 
  ∀ j : J, pi.lift p ≫ pi.π _ j = p j :=
assume j, by apply is_limit.fac  

@[hott]
def pi.lift_fac {J : Set.{u'}} {C : Type u} [category.{v} C] {f : J → C} 
  [has_product f] {P Q : C} (g : Q ⟶ P) (h : Π j : J, P ⟶ f j) :
  pi.lift (λ j, g ≫ h j) = g ≫ pi.lift h :=
let p := λ j : J, g ≫ h j, c := fan.mk _ p, lc := get_limit_cone (discrete.functor f) in  
begin 
  apply eq.inverse, apply is_limit.uniq lc.is_limit c, intro j, 
  rwr precategory.assoc, change g ≫ pi.lift h ≫ pi.π _ j = c.π.app j, rwr pi.lift_π_eq 
end  

@[hott]
def pi_hom {J : Set.{u'}} {C : Type u} [category.{v} C] [has_products.{v u u'} C] 
  {f g : J -> C} (h : Π j : J, f j ⟶ g j) : ∏ f ⟶ ∏ g :=
pi.lift (λ j : J, pi.π f j ≫ h j)

notation `∏h ` h:20 := pi_hom h

@[hott]
def pi_hom_id {J : Set.{u'}} {C : Type u} [category.{v} C] [has_products.{v u u'} C] (f : J -> C) : 
  pi_hom (λ j, 𝟙 (f j)) = 𝟙 (∏ f) :=
have H : (λ j, pi.π f j ≫ 𝟙 (f j)) = λ j, 𝟙 (∏ f) ≫ pi.π f j, from 
  begin apply eq_of_homotopy, intro j, hsimp end,  
begin change pi.lift (λ j, pi.π f j ≫ 𝟙 (f j)) = _, rwr H, rwr <- pi.hom_is_lift end  

@[hott]
def pi_hom_comp {J : Set.{u'}} {C : Type u} [category.{v} C] [has_products.{v u u'} C] 
  {f g h : J -> C}  (i₁ : Π j : J, f j ⟶ g j)  (i₂ : Π j : J, g j ⟶ h j) :
  (∏h i₁) ≫ (∏h i₂) = ∏h (λ j, i₁ j ≫ i₂ j) :=
have H : (λ j, pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.π g j ≫ i₂ j) = 
                                                          λ j, pi.π f j ≫ i₁ j ≫ i₂ j, from   
  begin 
    apply eq_of_homotopy, intro j, change pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.π g j ≫ i₂ j = _,
    rwr <- precategory.assoc, rwr pi.lift_π_eq, 
    change (pi.π f j ≫ i₁ j) ≫ i₂ j = pi.π f j ≫ i₁ j ≫ i₂ j, rwr precategory.assoc 
  end,
calc pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.lift (λ j, pi.π g j ≫ i₂ j) = 
           pi.lift (λ j, pi.lift (λ j, pi.π f j ≫ i₁ j) ≫ pi.π g j ≫ i₂ j) : 
                                                                      by rwr <- pi.lift_fac
     ... = pi.lift (λ j, pi.π f j ≫ i₁ j ≫ i₂ j) : by rwr H


/- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
@[hott, hsimp]
def parallel_pair_obj {C : Type u} [category.{v} C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair.{u} -> C :=
λ s, match s with
     | wp_pair.up := a
     | wp_pair.down := b
     end    

@[hott, hsimp]
def parallel_pair_map {C : Type u} [category.{v} C] {a b : C} 
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
def parallel_pair_map_id {C : Type u} [category.{v} C] {a b : C} 
  (f g : a ⟶ b) : ∀ s : walking_parallel_pair.{u}, 
  parallel_pair_map f g (𝟙 s) = 𝟙 (parallel_pair_obj f g s) :=
by intro s; hinduction s; hsimp; hsimp   

@[hott, hsimp]
def parallel_pair_map_comp {C : Type u} [category.{v} C] 
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
def parallel_pair {C : Type u} [category.{v} C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair.{u} ⥤ C :=
categories.functor.mk (parallel_pair_obj f g) 
                           (@parallel_pair_map _ _ _ _ f g) 
                           (parallel_pair_map_id f g) 
                           (@parallel_pair_map_comp _ _ _ _ f g)   

/- A cone over a parallel pair is called a `fork`. -/
@[hott]
abbreviation fork {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b) := 
  cone (parallel_pair f g) 

@[hott] 
def fork_map {C : Type u} [category.{v} C] {a b : C} {f g : a ⟶ b} (fk : fork f g) :
  fk.X ⟶ a := fk.π.app wp_up

@[hott]
def fork_eq {C : Type u} [category.{v} C] {a b : C} {f g : a ⟶ b} (fk : fork f g) :
  (fork_map fk) ≫ f = (fork_map fk) ≫ g :=
cone.fac fk wp_left ⬝ (cone.fac fk wp_right)⁻¹   
   
@[hott]
def fork.of_i {C : Type u} [category.{v} C] {a b c : C} 
  {f g : a ⟶ b} (i : c ⟶ a) (w : i ≫ f = i ≫ g) : fork f g :=
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

/- Limits of parallel pairs are `equalizers`. -/
@[hott]
class has_equalizer {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b) := 
  (has_limit : has_limit (parallel_pair f g))

@[hott, priority 100]
instance has_limit_of_has_equalizer {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b)
  [has_equalizer f g] : has_limit (parallel_pair f g) := 
has_equalizer.has_limit f g 

@[hott]
def equalizer {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b) [has_equalizer f g] :=
  limit (parallel_pair f g) 

@[hott] 
def equalizer_map {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b) [has_equalizer f g] :
  equalizer f g ⟶ a := fork_map (limit.cone (parallel_pair f g))    

@[hott] 
def equalizer_eq {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b) [has_equalizer f g] :
  equalizer_map f g ≫ f = equalizer_map f g ≫ g := fork_eq (limit.cone (parallel_pair f g)) 

@[hott]
def fork_lift {C : Type u} [category.{v} C] {a b : C} {f g : a ⟶ b} [has_equalizer f g] 
  (fk : fork f g) : fk.X ⟶ equalizer f g := 
(get_limit_cone (parallel_pair f g)).is_limit.lift fk  

@[hott]
def fork_lift_uniq {C : Type u} [category.{v} C] {a b : C} {f g : a ⟶ b} [has_equalizer f g] 
  (fk : fork f g) (m : fk.X ⟶ equalizer f g) : 
  m ≫ (equalizer_map f g) = fk.π.app wp_up -> m = fork_lift fk :=
begin 
  intro H, apply (get_limit_cone (parallel_pair f g)).is_limit.uniq fk,
  intro j, hinduction j, 
  { exact H }, 
  { change m ≫ (limit.cone (parallel_pair f g)).π.app wp_down = fk.π.app wp_down,
    rwr <- cone.fac (limit.cone (parallel_pair f g)) wp_left, 
    rwr <- cone.fac fk wp_left, rwr <- precategory.assoc m _ _, 
    change (m ≫ equalizer_map f g) ≫ _ = _, rwr H }
end  
    
@[hott]
class has_equalizers (C : Type u) [category.{v} C] := 
  (has_limit_of_shape : has_limits_of_shape walking_parallel_pair C)

@[hott]
instance has_equalizer_of_has_equalizers {C : Type u} [category.{v} C] 
  [has_equalizers C] {a b : C} (f g : a ⟶ b) : has_equalizer f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_equalizers.has_limit_of_shape C) (parallel_pair f g)⟩

@[hott, instance]
def has_equalizer_of_has_limits_of_shape {C : Type u} [category.{v} C] 
  [H : has_limits_of_shape walking_parallel_pair C] {a b : C} (f g : a ⟶ b) : 
  has_equalizer f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ H (parallel_pair f g)⟩ 

@[hott, instance]
def has_equalizers_of_has_limits (C : Type u) [category.{v} C] [H : has_limits C] : 
  has_equalizers C :=
has_equalizers.mk (@has_limits.has_limit_of_shape C _ H walking_parallel_pair _)

/- An equalizer is a subobject of the domain of the parallel pair. -/
@[hott]
def equalizer_as_subobject {C : Type u} [category.{v} C] {a b : C} (f g : a ⟶ b) 
  [has_equalizer f g] : subobject a :=
begin
  let e := equalizer_map f g, let He : e ≫ f = e ≫ g := equalizer_eq f g,
  fapply subobject.mk,
  { exact equalizer f g },
  { exact e },
  { intros d h h' Hm, 
    have Hhe : (h ≫ e) ≫ f = (h ≫ e) ≫ g, from 
      (precategory.assoc h e f) ⬝ ap (category_struct.comp h) He ⬝ (precategory.assoc h e g)⁻¹,
    have Hhf : h = fork_lift (fork.of_i (h ≫ e) Hhe), from 
      fork_lift_uniq (fork.of_i (h ≫ e) Hhe) h rfl,  
    have Hh'e : (h' ≫ e) ≫ f = (h' ≫ e) ≫ g, from
      (precategory.assoc h' e f) ⬝ ap (category_struct.comp h') He ⬝ (precategory.assoc h' e g)⁻¹,
    have Hh'f : h' = fork_lift (fork.of_i (h' ≫ e) Hh'e), from 
      fork_lift_uniq (fork.of_i (h' ≫ e) Hh'e) h' rfl,
    rwr Hhf, rwr Hh'f, 
    let F : Π (h'': d ⟶ a), (h'' ≫ f = h'' ≫ g) -> (d ⟶ equalizer f g) := 
                                                     (λ h'' p, fork_lift (fork.of_i h'' p)),
    change F (h ≫ e) Hhe = F (h' ≫ e) Hh'e, fapply apd011 F, 
    exact Hm, apply pathover_of_tr_eq, exact is_set.elim _ _ }
end  


/- The category of sets has all limits. 

   The limit cone is constructed as the sections of the functor map satisfying the 
   compatibility conditions of the indexing category. We define this predicate separately, 
   for use later on.
   
   Note that the limit cone vertex may be the empty set - then all cones over the functor `F`
   are empty because otherwise they cannot factorize through the empty set. 
   
   Also not that the cone must live in an uiniverse both containing the diagram set 
   and the sets ordered according to the diagram. -/
@[hott]
def set_limit_pred {J : Set.{u'}} [precategory.{v'} J] (F : J ⥤ Set) : 
  Subset (Sections F.obj) :=
λ s, prop_resize (to_Prop (∀ (j k : J) (f : j ⟶ k), F.map f (s j) = s k)) 

@[hott, reducible]
def set_cone {J : Set.{u'}} [precategory.{v'} J] (F : J ⥤ Set) : cone F :=
begin
  fapply cone.mk, 
  /- The limit cone vertex set -/
  { exact pred_Set (set_limit_pred F) }, 
  { fapply nat_trans.mk, 
    /- the leg maps of the limit cone -/
    { intro j, exact λ u, u.1 j },
    /- compatibility of the leg maps -/
    { intros j k f, hsimp, 
      fapply eq_of_homotopy, intro u, hsimp, change u.1 k = F.map f (u.1 j), 
      rwr (prop_resize_to_prop u.2 j k f) } }
end  

@[hott, reducible]
def set_cone_is_limit {J : Set} [precategory J] (F : J ⥤ Set) :
  is_limit (set_cone F) :=
begin 
  fapply is_limit.mk,
  /- the lift from the limit cone to another cone-/ 
  { intro s, intro x, fapply sigma.mk, 
    { intro j, exact s.π.app j x },
    { hsimp, apply prop_to_prop_resize, intros j k f, 
      exact (homotopy_of_eq (s.π.naturality f) x)⁻¹ } },
  /- factorising the lift with limit cone legs -/    
  { intros s j, hsimp, apply eq_of_homotopy, 
    intro x, refl },
  /- uniqueness of lift -/  
  { intros s m lift_m, hsimp, apply eq_of_homotopy,
    intro x, hsimp, fapply sigma.sigma_eq, 
    { exact eq_of_homotopy (λ j, @homotopy_of_eq s.X _ _ _ (lift_m j) x) },
    { hsimp, apply pathover_of_tr_eq, apply is_prop.elim } }  
end

@[hott, reducible]
def set_limit_cone {J : Set} [precategory J] (F : J ⥤ Set) : limit_cone F :=
  limit_cone.mk (set_cone F) (set_cone_is_limit F)

@[hott, instance]
def set_has_limit {J : Set} [precategory J] (F : J ⥤ Set) : has_limit F :=
  has_limit.mk (set_limit_cone F)

@[hott, instance]
def set_has_limits_of_shape (J : Set) [precategory J] : has_limits_of_shape J Set :=
  has_limits_of_shape.mk (λ F, set_has_limit F)     

@[hott, instance]
def set_has_products : has_products Set :=
  ⟨λ J : Set, @set_has_limits_of_shape (discrete J) _⟩

@[hott, instance]
def set_has_product {J : Set} (f : J -> Set) : has_product f :=
  ⟨set_has_limit (discrete.functor f)⟩

@[hott]
def Set_prod_sections {I : Set} {U : I -> Set} : (∏ U) = Sections U :=
begin
  change pred_Set (λ s : Sections U, set_limit_pred (discrete.functor U) s) = Sections U, 
  have pred_eq : (λ s : Sections U, set_limit_pred (discrete.functor U) s) = (λ s, True), from
    begin 
      apply eq_of_homotopy, intro s, hsimp, apply prop_iff_eq, 
      { intro p, exact true.intro },
      { intro t, apply prop_to_prop_resize, intros j k f, 
        change (f ▸[λ k : discrete I, U j ⟶ U k] 𝟙 (U j)) (s j) = s k, 
        hinduction f, rwr idp_tr } 
    end,
  rwr pred_eq, apply car_eq_to_set_eq, 
  apply ap trunctype.carrier (total_pred_Set_eq_Set (Sections U))
end 


/- The full subcategory on a subtype of a category with limits has limits if the limit
   of a diagram of objects of the subtype is also in the subtype. -/
@[hott]
def limit_closed_subtype {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C]   
  (P : C -> trunctype.{0} -1) (F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))) :=
∀ (lc : limit_cone (embed F)), (P lc.cone.X).carrier

@[hott] 
def emb_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C]   
  {P : C -> trunctype.{0} -1} {F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))} 
  (s : cone F) : cone (embed F) :=
begin
  fapply cone.mk, 
  { exact s.X.1 },
  { fapply nat_trans.mk,
    { intro j, exact s.π.app j },
    { intros j k f, exact s.π.naturality f } }
end  

@[hott]
def subcat_limit_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C]   
  {P : C -> trunctype.{0} -1} {F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))} 
  (lc : limit_cone (embed F)) (lim_clos : (P lc.cone.X).carrier) : 
  limit_cone F :=
begin
  fapply limit_cone.mk,
  { fapply cone.mk,
    { exact ⟨lc.cone.X, lim_clos⟩ },
    { fapply nat_trans.mk, 
      { intro j, exact lc.cone.π.app j },
      { intros j k f, exact lc.cone.π.naturality f } } },
  { fapply is_limit.mk,
    { intro s, exact lc.is_limit.lift (emb_cone s) },
    { intros s j, exact lc.is_limit.fac (emb_cone s) j },
    { intros s m j, exact lc.is_limit.uniq (emb_cone s) m j } }
end  

@[hott, instance]
def subcat_has_limit {J : Set} [precategory J] {C : Type u} [category.{v} C]   
  {P : C -> trunctype.{0} -1} {F : J ⥤ (sigma.subtype (λ c : C, ↥(P c)))} 
  [has_limit (embed F)] (lim_clos : limit_closed_subtype P F) : has_limit F :=
has_limit.mk (subcat_limit_cone (get_limit_cone (embed F)) 
             (lim_clos (get_limit_cone (embed F))))

@[hott, instance]
def subcat_has_limits_of_shape (J : Set) [precategory J] {C : Type u} [category.{v} C]   
  {P : C -> trunctype.{0} -1} [has_limits_of_shape J C] 
  (lim_clos : ∀ F : J ⥤ (sigma.subtype (λ c : C, ↥(P c))), 
                                                  @limit_closed_subtype J _ _ _ P F) : 
  has_limits_of_shape J (sigma.subtype (λ c : C, ↥(P c))) :=
has_limits_of_shape.mk (λ F, subcat_has_limit (lim_clos F))     

@[hott, instance]
def subcat_has_products {C : Type u} [category.{v} C] {P : C -> trunctype.{0} -1} 
  [has_products C] 
  (lim_clos : ∀ (J : Set) (F : (discrete J) ⥤ (sigma.subtype (λ c : C, ↥(P c)))), 
                                  limit_closed_subtype P F) : 
  has_products (sigma.subtype (λ c : C, ↥(P c))) :=
⟨λ J : Set, @subcat_has_limits_of_shape (discrete J) _ _ _ _ 
             (has_limits_of_shape_of_has_products J C) (lim_clos J)⟩

end categories.limits

end hott