import categories.limits

universes v v' u u' w
hott_theory

namespace hott
open hott.categories hott.categories.limits

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
  (f : a ⟶ c) (g : b ⟶ c) (i : d ⟶ a) (j : d ⟶ b) (w : i ≫ f = j ≫ g) : square f g :=
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


end categories.pullbacks

end hott     