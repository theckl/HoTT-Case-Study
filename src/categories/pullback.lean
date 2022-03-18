import categories.limits categories.adjoints

universes v v' u u' w
hott_theory

namespace hott
open hott.categories hott.categories.limits hott.is_trunc categories.adjoints

namespace categories.pullbacks

/- `orthogonal_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
   common codomain. -/
@[hott, hsimp]
def orthogonal_pair_obj {C : Type u} [category.{v} C] {a b c: C} 
  (f : a ⟶ c) (g : b ⟶ c) : orthogonal_wedge.{u} -> C :=
λ s, match s with
     | ow_node.left := a
     | ow_node.base := c
     | ow_node.upper := b
     end    

@[hott, hsimp]
def orthogonal_pair_map {C : Type u} [category.{v} C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : Π {s t : orthogonal_wedge.{u}}, 
  (s ⟶ t) -> (orthogonal_pair_obj f g s ⟶ orthogonal_pair_obj f g t) :=
assume s t, 
match s, t with
  | ow_node.left, ow_node.left := assume h, 𝟙 a --id
  | ow_node.left, ow_node.base := assume h, f --right arrow
  | ow_node.left, ow_node.upper := begin intro h, hinduction h end
  | ow_node.base, ow_node.left := begin intro h, hinduction h end
  | ow_node.base, ow_node.base := assume h, 𝟙 c --id
  | ow_node.base, ow_node.upper := begin intro h, hinduction h end
  | ow_node.upper, ow_node.left := begin intro h, hinduction h end
  | ow_node.upper, ow_node.base := assume h, g --down arrow
  | ow_node.upper, ow_node.upper := assume h, 𝟙 b --id
end 

@[hott, hsimp]
def orthogonal_pair_map_id {C : Type u} [category.{v} C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : ∀ s : orthogonal_wedge.{u}, 
  orthogonal_pair_map f g (𝟙 s) = 𝟙 (orthogonal_pair_obj f g s) :=
begin intro s, hinduction s, hsimp, hsimp, hsimp end 

@[hott, hsimp]
def orthogonal_pair_map_comp {C : Type u} [category.{v} C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : ∀ {s t u : orthogonal_wedge.{u}} 
  (h : s ⟶ t) (i : t ⟶ u), orthogonal_pair_map f g (h ≫ i) = 
                  (orthogonal_pair_map f g h) ≫ (orthogonal_pair_map f g i) :=
begin 
  intros s t u h i; hinduction s; hinduction t; hinduction u; 
  hsimp; hinduction i; hinduction h 
end

@[hott]
def orthogonal_pair {C : Type u} [category.{v} C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : orthogonal_wedge.{u} ⥤ C :=
categories.functor.mk (orthogonal_pair_obj f g) 
                           (@orthogonal_pair_map _ _ _ _ _ f g) 
                           (orthogonal_pair_map_id f g) 
                           (@orthogonal_pair_map_comp _ _ _ _ _ f g)  

/- Limits of orthogonal pairs are `pullbacks`. -/
@[hott]
class has_pullback {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) := 
  (has_limit : has_limit (orthogonal_pair f g))

@[hott, priority 100]
instance has_limit_of_has_pullback {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c)
  (g : b ⟶ c) [has_pullback f g] : has_limit (orthogonal_pair f g) := 
has_pullback.has_limit f g 

@[hott]
def pullback {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] := limit (orthogonal_pair f g)   

@[hott]
def pullback_homo_l {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] : pullback f g ⟶ a :=
limit_leg (orthogonal_pair f g) ow_node.left  

@[hott]
def pullback_homo_t {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] : pullback f g ⟶ b :=
limit_leg (orthogonal_pair f g) ow_node.upper 

@[hott]
class has_pullbacks (C : Type u) [category.{v} C] := 
  (has_limit_of_shape : has_limits_of_shape orthogonal_wedge C)

@[hott]
instance has_pullback_of_has_pullbacks {C : Type u} [category.{v} C] 
  [has_pullbacks C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : has_pullback f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_pullbacks.has_limit_of_shape C) (orthogonal_pair f g)⟩

@[hott, instance]
def has_pullback_of_has_limits_of_shape {C : Type u} [category.{v} C] 
  [H : has_limits_of_shape orthogonal_wedge C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : 
  has_pullback f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ H (orthogonal_pair f g)⟩ 

@[hott, instance]
def has_pullbacks_of_has_limits (C : Type u) [category.{v} C] [H : has_limits C] : 
  has_pullbacks C :=
has_pullbacks.mk (@has_limits.has_limit_of_shape C _ H orthogonal_wedge _)


/- A cone over an orthogonal pair is called a `square`. -/
@[hott]
abbreviation square {C : Type u} [category.{v} C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) := cone (orthogonal_pair f g) 

@[hott]
def square.of_i_j {C : Type u} [category.{v} C] {a b c d : C} 
  {f : a ⟶ c} {g : b ⟶ c} {i : d ⟶ a} {j : d ⟶ b} (w : i ≫ f = j ≫ g) : square f g :=
have π : constant_functor ↥orthogonal_wedge C d ⟹ orthogonal_pair f g, from
  let app :=  @ow_node.rec (λ x, d ⟶ (orthogonal_pair f g).obj x) i (i ≫ f) j in
  have naturality : ∀ (x x' : orthogonal_wedge) (h : x ⟶ x'), 
          ((constant_functor ↥orthogonal_wedge C d).map h) ≫ (app x') = 
           (app x) ≫ ((orthogonal_pair f g).map h), from 
  begin 
    intros x x' h; hinduction x; hinduction x'; hinduction h; hsimp,
    { change i ≫ f = i ≫ f, refl },
    { change i ≫ f = j ≫ g, exact w }  
  end,           
  nat_trans.mk app naturality,   
cone.mk d π 

@[hott]
def square_left {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) : S.X ⟶ a := S.π.app ow_left

@[hott]
def square_top {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) : S.X ⟶ b := S.π.app ow_upper

@[hott]
def square_eq {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) : (square_left S) ≫ f = (square_top S) ≫ g :=
calc (square_left S) ≫ f = (S.π.app ow_left) ≫ (orthogonal_pair f g).map ow_right : rfl 
     ... = S.π.app ow_base : by rwr cone.fac S ow_right 
     ... = (S.π.app ow_upper) ≫ (orthogonal_pair f g).map ow_down : 
           by rwr cone.fac S ow_down
     ... = (square_top S) ≫ g : rfl

@[hott] 
def pullback_eq {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c} 
  [has_pullback f g] : pullback_homo_l f g ≫ f = pullback_homo_t f g ≫ g :=
square_eq (limit.cone (orthogonal_pair f g))  

@[hott]
def pullback_lift {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : S.X ⟶ pullback f g :=
(get_limit_cone (orthogonal_pair f g)).is_limit.lift S 

@[hott]
def pb_lift_eq_l {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : 
  pullback_lift S ≫ pullback_homo_l f g = square_left S :=
(get_limit_cone (orthogonal_pair f g)).is_limit.fac S ow_left  

@[hott]
def pb_lift_eq_t {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : 
  pullback_lift S ≫ pullback_homo_t f g = square_top S :=
(get_limit_cone (orthogonal_pair f g)).is_limit.fac S ow_upper  

@[hott]
def pullback_uniq {C : Type u} [category.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : Π (h : S.X ⟶ pullback f g), 
  h ≫ pullback_homo_l f g = square_left S -> h ≫ pullback_homo_t f g = square_top S ->
  h = pullback_lift S :=
assume h pl pt,
have w : Π (ow : orthogonal_wedge), h ≫ (limit.cone (orthogonal_pair f g)).π.app ow =
                                    S.π.app ow, from  
  begin 
    intro ow, hinduction ow, 
    { exact pl }, 
    { change h ≫ (limit.cone (orthogonal_pair f g)).π.app ow_base = S.π.app ow_base, 
      rwr <- cone.fac S ow_right, 
      rwr <- cone.fac (limit.cone (orthogonal_pair f g)) ow_right, 
      rwr <- precategory.assoc, change (h ≫ pullback_homo_l f g) ≫ _ = _, rwr pl }, 
    { exact pt }
  end,
(get_limit_cone (orthogonal_pair f g)).is_limit.uniq S h w   

@[hott]
def mono_is_stable {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  (H : is_mono g) [has_pullback f g] : is_mono (pullback_homo_l f g) :=
begin 
  intros d h₁ h₂ ph, 
  have ph' : (h₁ ≫ (pullback_homo_t f g)) ≫ g = (h₂ ≫ (pullback_homo_t f g)) ≫ g, from 
    calc (h₁ ≫ (pullback_homo_t f g)) ≫ g 
             = h₁ ≫ (pullback_homo_t f g) ≫ g : by rwr precategory.assoc
         ... = h₁ ≫ (pullback_homo_l f g) ≫ f : by rwr pullback_eq
         ... = (h₁ ≫ (pullback_homo_l f g)) ≫ f : by rwr precategory.assoc
         ... = (h₂ ≫ (pullback_homo_l f g)) ≫ f : by rwr ph
         ... = h₂ ≫ (pullback_homo_l f g) ≫ f : by rwr precategory.assoc
         ... = h₂ ≫ (pullback_homo_t f g) ≫ g : by rwr pullback_eq
         ... = (h₂ ≫ (pullback_homo_t f g)) ≫ g : by rwr precategory.assoc,
  have ph'' : h₁ ≫ (pullback_homo_t f g) = h₂ ≫ (pullback_homo_t f g), from H _ _ _ ph',
  have ph₁ : (h₁ ≫ (pullback_homo_l f g)) ≫ f = (h₁ ≫ (pullback_homo_t f g)) ≫ g, by
    rwr precategory.assoc; rwr pullback_eq; rwr <- precategory.assoc,   
  have ph₂ : (h₂ ≫ (pullback_homo_l f g)) ≫ f = (h₂ ≫ (pullback_homo_t f g)) ≫ g, by
    rwr precategory.assoc; rwr pullback_eq; rwr <- precategory.assoc,  
  let S₁ : square f g := square.of_i_j ph₁, let S₂ : square f g := square.of_i_j ph₂,
  have sl₁ : h₁ ≫ pullback_homo_l f g = square_left S₁, from idp,
  have st₁ : h₁ ≫ pullback_homo_t f g = square_top S₁, from idp,
  have sl₂ : h₂ ≫ pullback_homo_l f g = square_left S₁, from ph⁻¹ ⬝ sl₁,
  have st₂ : h₂ ≫ pullback_homo_t f g = square_top S₁, from ph''⁻¹ ⬝ st₁,
  calc h₁ = pullback_lift S₁ : pullback_uniq S₁ h₁ sl₁ st₁
       ... = h₂ : (pullback_uniq S₁ h₂ sl₂ st₂)⁻¹ 
end  

@[hott]
def pullback_subobject  {C : Type u} [category.{v} C] {a c : C} (f : a ⟶ c) 
  (b : subobject c) [has_pullback f b.hom] : subobject a :=
subobject.mk (pullback f b.hom) (pullback_homo_l f b.hom) 
                                (mono_is_stable f b.hom b.is_mono)

def pullback_subobject_hom  {C : Type u} [category.{v} C] {a c : C} (f : a ⟶ c) 
  {b₁ b₂ : subobject c} [has_pullback f b₁.hom] [has_pullback f b₂.hom] 
  (i : b₁ ⟶ b₂) : pullback_subobject f b₁ ⟶ pullback_subobject f b₂ :=
begin
  have w : (pullback_subobject f b₁).hom ≫ f = 
                              (pullback_homo_t f b₁.hom ≫ i.hom_obj) ≫ b₂.hom, from 
    begin 
      change pullback_homo_l f b₁.hom ≫ f = _, rwr pullback_eq, 
      rwr precategory.assoc, rwr i.fac 
    end, 
  fapply hom_of_monos.mk, 
  { exact pullback_lift (square.of_i_j w) }, 
  { exact pb_lift_eq_l (square.of_i_j w) } 
end   

@[hott]
def pb_subobj_functor {C : Type u} [category.{v} C] {a c : C} (f : a ⟶ c) 
  [has_pullbacks.{v u u} C] : subobject c ⥤ subobject a :=
categories.functor.mk (λ b : subobject c, pullback_subobject f b)
                      (λ b₁ b₂ i, pullback_subobject_hom f i)
                      (λ b, is_prop.elim _ _)
                      (λ b₁ b₂ b₃ i₁ i₂, is_prop.elim _ _) 


@[hott]
def image_is_stable {C : Type u} [category.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c)
  [has_images C] [has_pullbacks.{v u u} C] := 
  hom.image (pullback_homo_l f g) = pullback_subobject f (hom.image g) 

@[hott]
class has_stable_images (C : Type u) [category.{v} C] :=
  (has_im : has_images C)
  (has_pb : has_pullbacks.{v u u} C)
  (stable_im : Π (a b c : C) (f : a ⟶ c) (g : b ⟶ c), image_is_stable f g)

@[hott, instance]
def has_images_of_has_stable_images {C : Type u} [category.{v} C] 
  [H : has_stable_images C] : has_images C := H.has_im

@[hott, instance]
def has_pullbacks_of_has_stable_images {C : Type u} [category.{v} C] 
  [H : has_stable_images C] : has_pullbacks C := H.has_pb


/- The pullback functors of subobjects has a left adjoint. -/


end categories.pullbacks

end hott     