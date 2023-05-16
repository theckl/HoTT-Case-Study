import categories.limits categories.adjoints

universes v v' u u' w
hott_theory

namespace hott
open hott.precategories hott.categories hott.categories.limits hott.is_trunc 
     categories.adjoints hott.set hott.trunc 

namespace categories.pullbacks

/- `orthogonal_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
   common codomain. -/
@[hott, hsimp]
def orthogonal_pair_obj {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : orthogonal_wedge -> C :=
λ s, match s with
     | inf_w_node.tip ow_node.left := a
     | inf_w_node.tip ow_node.upper := b
     | inf_w_node.base ow_leg_node := c
     
     end    

@[hott, hsimp]
def orthogonal_pair_map {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : Π {s t : orthogonal_wedge}, 
  (s ⟶ t) -> (orthogonal_pair_obj f g s ⟶ orthogonal_pair_obj f g t) :=
assume s t, 
match s, t with
  | inf_w_node.tip ow_node.left, inf_w_node.tip ow_node.left := assume h, 𝟙 a --id
  | inf_w_node.tip ow_node.left, inf_w_node.base ow_leg_node := assume h, f --right arrow
  | inf_w_node.tip ow_node.left, inf_w_node.tip ow_node.upper := 
      begin intro h, hinduction (own_encode h) end
  | inf_w_node.base ow_leg_node , inf_w_node.tip ow_node.left := 
      begin intro h, hinduction h end    
  | inf_w_node.base ow_leg_node, inf_w_node.base _ := assume h, 𝟙 c --id
  | inf_w_node.base ow_leg_node , inf_w_node.tip ow_node.upper :=    
      begin intro h, hinduction h end
  | inf_w_node.tip ow_node.upper, inf_w_node.tip ow_node.left := 
      begin intro h, hinduction (own_encode h) end
  | inf_w_node.tip ow_node.upper, inf_w_node.base ow_leg_node := assume h, g --down arrow
  | inf_w_node.tip ow_node.upper, inf_w_node.tip ow_node.upper := assume h, 𝟙 b --id
end 

@[hott, hsimp]
def orthogonal_pair_map_id {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : ∀ s : orthogonal_wedge, 
  orthogonal_pair_map f g (𝟙 s) = 𝟙 (orthogonal_pair_obj f g s) :=
begin intro s, hinduction s with n, hinduction n, all_goals { hsimp } end 

@[hott, hsimp]
def orthogonal_pair_map_comp {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : ∀ {s t u : orthogonal_wedge} 
  (h : s ⟶ t) (i : t ⟶ u), orthogonal_pair_map f g (h ≫ i) = 
                  (orthogonal_pair_map f g h) ≫ (orthogonal_pair_map f g i) :=
begin 
  intros s t u h i; 
  hinduction s with n₁, hinduction n₁, 
  all_goals { hinduction t with n₂, try { hinduction n₂} },
  all_goals { hinduction u with n₃, try { hinduction n₃} },
  all_goals { try { solve1 { hsimp } } }, 
  all_goals { try { solve1 { hinduction (own_encode i) } } }, 
  all_goals { try { solve1 { hinduction (own_encode h) } } },
  all_goals { try { solve1 { hinduction i } } },
  all_goals { try { solve1 { hinduction h } } } 
end

@[hott]
def orthogonal_pair {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : orthogonal_wedge ⥤ C :=
precategories.functor.mk (orthogonal_pair_obj f g) 
                           (@orthogonal_pair_map _ _ _ _ _ f g) 
                           (orthogonal_pair_map_id f g) 
                           (@orthogonal_pair_map_comp _ _ _ _ _ f g) 

/- Symmetry of orthogonal pairs -/
@[hott]
def sym_orthogonal_pair_obj {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : Π (ow : orthogonal_wedge), 
  (orthogonal_pair g f).obj ow = 
  (orthogonal_wedge_iso.hom ⋙ orthogonal_pair f g).obj ow :=
begin
  exact (λ (ow : ↥orthogonal_wedge), 
              inf_w_node.rec (λ (n : ↥ow_leg_node), ow_node.rec idp idp n) idp ow)
end              

@[hott]
def sym_orthogonal_pair {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) : 
  orthogonal_pair g f = (orthogonal_wedge_iso.hom ⋙ orthogonal_pair f g) :=
begin
  fapply functor_eq, 
  { exact eq_of_homotopy (sym_orthogonal_pair_obj f g) },
  { apply deq_of_homotopy3', intros ow₁ ow₂ h, 
    hinduction ow₁ with n₁, hinduction n₁,
    all_goals { hinduction ow₂ with n₂, hinduction n₂ }, 
    all_goals { try { solve1 { hinduction (own_encode h) } } },
    all_goals { try { solve1 { hinduction h } } }, 
    all_goals { try { solve1 { apply pathover_of_tr_eq, 
      apply eq.concat (@fn_eq_tr_fn2 orthogonal_wedge C _ _ (orthogonal_pair g f).obj 
              (orthogonal_wedge_iso.hom ⋙ orthogonal_pair f g).obj 
              (eq_of_homotopy (sym_orthogonal_pair_obj f g)) (λ c₁ c₂ : C, c₁ ⟶ c₂) 
              ((orthogonal_pair g f).map h)), 
      rwr ap10_eq_of_homotopy } } } }
end
 

/- Limits of orthogonal pairs are `pullbacks`. -/
@[hott]
class has_pullback {C : Type _} [is_cat C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) := 
  (has_limit : has_limit (orthogonal_pair f g))

@[hott, instance]
def has_limit_of_has_pullback {C : Type _} [is_cat C] {a b c : C} (f : a ⟶ c)
  (g : b ⟶ c) [has_pullback f g] : has_limit (orthogonal_pair f g) := 
has_pullback.has_limit f g 

@[hott]
def pullback {C : Type _} [is_cat C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] := limit (orthogonal_pair f g)  

@[hott]
def pullback_homo_l {C : Type _} [is_cat C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] : pullback f g ⟶ a :=
limit_leg (orthogonal_pair f g) (inf_w_node.tip ow_node.left)  

@[hott]
def pullback_homo_t {C : Type _} [is_cat C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] : pullback f g ⟶ b :=
limit_leg (orthogonal_pair f g) (inf_w_node.tip ow_node.upper) 

@[hott]
class has_pullbacks (C : Type _) [is_cat C] := 
  (has_limit_of_shape : has_limits_of_shape orthogonal_wedge C)

@[hott]
instance has_pullback_of_has_pullbacks {C : Type _} [is_cat C] 
  [has_pullbacks C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : has_pullback f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_pullbacks.has_limit_of_shape C) (orthogonal_pair f g)⟩

@[hott, instance]
def has_pullback_of_has_limits_of_shape {C : Type _} [is_cat C] 
  [H : has_limits_of_shape orthogonal_wedge C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : 
  has_pullback f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ H (orthogonal_pair f g)⟩ 

@[hott, instance]
def has_pullbacks_of_has_limits (C : Type _) [is_cat C] [H : has_limits C] : 
  has_pullbacks C :=
has_pullbacks.mk (@has_limits.has_limit_of_shape C _ H orthogonal_wedge _)


/- A cone over an orthogonal pair is called a `square`. -/
@[hott]
abbreviation square {C : Type _} [is_cat C] {a b c : C} 
  (f : a ⟶ c) (g : b ⟶ c) := cone (orthogonal_pair f g) 

@[hott]
def square.of_i_j {C : Type _} [is_cat C] {a b c d : C} 
  {f : a ⟶ c} {g : b ⟶ c} {i : d ⟶ a} {j : d ⟶ b} (w : i ≫ f = j ≫ g) : square f g :=
begin
  fapply cone.mk d, fapply nat_trans.mk,
  { intro s, hinduction s with n, hinduction n, exact i, exact j, exact i ≫ f },
  { intros s₁ s₂ h, hinduction s₁ with n₁, all_goals { hinduction s₂ with n₂ },
    all_goals { try { hinduction n₁ } }, all_goals { try { hinduction n₂ } },
    all_goals { try { solve1 { hinduction h } } },
    all_goals { try { solve1 { hinduction (own_encode h) } } },
    all_goals { try { rwr is_precat.id_comp, change _ = _ ≫ 𝟙 _, rwr is_precat.comp_id } },
    all_goals { try { rwr is_precat.id_comp } },
    rwr w } 
end

@[hott]
def square_left {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) : S.X ⟶ a := S.π.app ow_left

@[hott]
def square_top {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) : S.X ⟶ b := S.π.app ow_upper

@[hott]
def square_eq {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) : (square_left S) ≫ f = (square_top S) ≫ g :=
calc (square_left S) ≫ f = (S.π.app (inf_w_tip ow_node.left)) ≫ (orthogonal_pair f g).map 
                                                  (inf_w_leg ow_node.left) : rfl 
     ... = S.π.app ow_base : by rwr cone.fac S (inf_w_leg ow_node.left) 
     ... = (S.π.app (inf_w_tip ow_node.upper)) ≫ (orthogonal_pair f g).map (inf_w_leg ow_node.upper) : 
           by rwr cone.fac S (inf_w_leg ow_node.upper)
     ... = (square_top S) ≫ g : rfl

@[hott] 
def pullback_eq {C : Type _} [is_cat C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  [has_pullback f g] : pullback_homo_l f g ≫ f = pullback_homo_t f g ≫ g :=
square_eq (limit.cone (orthogonal_pair f g))  

@[hott]
def pullback_lift {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : S.X ⟶ pullback f g :=
(get_limit_cone (orthogonal_pair f g)).is_limit.lift S 

@[hott]
def pb_lift_eq_l {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : 
  pullback_lift S ≫ pullback_homo_l f g = square_left S :=
(get_limit_cone (orthogonal_pair f g)).is_limit.fac S ow_left  

@[hott]
def pb_lift_eq_t {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : 
  pullback_lift S ≫ pullback_homo_t f g = square_top S :=
(get_limit_cone (orthogonal_pair f g)).is_limit.fac S ow_upper  

@[hott]
def pullback_uniq {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : Π (h : S.X ⟶ pullback f g), 
  h ≫ pullback_homo_l f g = square_left S -> h ≫ pullback_homo_t f g = square_top S ->
  h = pullback_lift S :=
assume h pl pt,
have w : Π (ow : orthogonal_wedge), h ≫ (limit.cone (orthogonal_pair f g)).π.app ow =
                                    S.π.app ow, from  
  begin 
    intro ow, hinduction ow with n, hinduction n, 
    { exact pl }, 
    { exact pt },
    { change h ≫ (limit.cone (orthogonal_pair f g)).π.app inf_w_base = _, 
      rwr <- cone.fac (limit.cone (orthogonal_pair f g)) (inf_w_leg ow_node.left),
      rwr <- is_precat.assoc, change (h ≫ pullback_homo_l f g) ≫ _ = _, rwr pl, 
      change _ = S.π.app inf_w_base, rwr <- cone.fac S (inf_w_leg ow_node.left) }, 
  end,
(get_limit_cone (orthogonal_pair f g)).is_limit.uniq S h w 

/- Pullbacks are symmetric in the two legs.
   
   The existence of the symmetric pullback derived from an instance of the pullback
   cannot be set up as an instance because this would cause infinite loops when 
   determining class instances. 
   
   Usually, we just assume that all pullbacks exist in a category. -/
@[hott]
def has_sym_pullback {C : Type u} [is_cat.{v} C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c)
  [pull_fg : has_pullback f g] : has_pullback g f :=
begin
  apply has_pullback.mk, rwr sym_orthogonal_pair f g, 
  exact @diag_iso_has_lim_to_has_lim'.{v u 0 0 0 0} _ _ _ _ orthogonal_wedge_iso _
        pull_fg.has_limit        
end

@[hott]
def sym_pullback_eq {C : Type u} [is_cat.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  [has_pullback.{u v} f g] [has_pullback.{u v} g f] : pullback f g = pullback g f :=
(diag_iso_lim_eq_lim.{v u 0 0 0 0} orthogonal_wedge_iso _) ⬝ 
(@diag_eq_lim_eq_lim Orthogonal_Wedge _ _ _ (orthogonal_pair g f) 
  (sym_orthogonal_pair f g)⁻¹ 
  (diag_iso_has_lim_to_has_lim'.{v u 0 0 0 0} orthogonal_wedge_iso) _)

@[hott]
def sym_pullback_legs_eq {C : Type u} [is_cat.{v} C] {a b c : C} (f : a ⟶ c) 
  (g : b ⟶ c) [has_pullback.{u v} f g] [has_pullback.{u v} g f] : 
  (idtoiso sym_pullback_eq).hom ≫ pullback_homo_l g f = pullback_homo_t f g :=
begin
  change (idtoiso (diag_iso_lim_eq_lim _ _ ⬝ _)).hom ≫ _ = _, rwr <- idtoiso_comp_eq, 
  rwr is_precat.assoc,
  sorry
end


/- The stability of monomorphisms under pullbacks can be used to construct pullbacks 
   of subobjects. -/
@[hott]
def mono_is_stable {C : Category} {a b c : C} (f : a ⟶ c) (g : b ⟶ c) 
  (H : is_mono g) [has_pullback f g] : is_mono (pullback_homo_l f g) :=
begin 
  intros d h₁ h₂ ph, 
  have ph' : (h₁ ≫ (pullback_homo_t f g)) ≫ g = (h₂ ≫ (pullback_homo_t f g)) ≫ g, from 
    calc (h₁ ≫ (pullback_homo_t f g)) ≫ g 
             = h₁ ≫ (pullback_homo_t f g) ≫ g : by rwr is_precat.assoc
         ... = h₁ ≫ (pullback_homo_l f g) ≫ f : by rwr pullback_eq
         ... = (h₁ ≫ (pullback_homo_l f g)) ≫ f : by rwr is_precat.assoc
         ... = (h₂ ≫ (pullback_homo_l f g)) ≫ f : by rwr ph
         ... = h₂ ≫ (pullback_homo_l f g) ≫ f : by rwr is_precat.assoc
         ... = h₂ ≫ (pullback_homo_t f g) ≫ g : by rwr pullback_eq
         ... = (h₂ ≫ (pullback_homo_t f g)) ≫ g : by rwr is_precat.assoc,
  have ph'' : h₁ ≫ (pullback_homo_t f g) = h₂ ≫ (pullback_homo_t f g), from H _ _ _ ph',
  have ph₁ : (h₁ ≫ (pullback_homo_l f g)) ≫ f = (h₁ ≫ (pullback_homo_t f g)) ≫ g, by
    rwr is_precat.assoc; rwr pullback_eq; rwr <- is_precat.assoc,   
  have ph₂ : (h₂ ≫ (pullback_homo_l f g)) ≫ f = (h₂ ≫ (pullback_homo_t f g)) ≫ g, by
    rwr is_precat.assoc; rwr pullback_eq; rwr <- is_precat.assoc,  
  let S₁ : square f g := square.of_i_j ph₁, let S₂ : square f g := square.of_i_j ph₂,
  have sl₁ : h₁ ≫ pullback_homo_l f g = square_left S₁, from idp,
  have st₁ : h₁ ≫ pullback_homo_t f g = square_top S₁, from idp,
  have sl₂ : h₂ ≫ pullback_homo_l f g = square_left S₁, from ph⁻¹ ⬝ sl₁,
  have st₂ : h₂ ≫ pullback_homo_t f g = square_top S₁, from ph''⁻¹ ⬝ st₁,
  calc h₁ = pullback_lift S₁ : pullback_uniq S₁ h₁ sl₁ st₁
       ... = h₂ : (pullback_uniq S₁ h₂ sl₂ st₂)⁻¹ 
end  

@[hott]
def pullback_subobject  {C : Category} {a c : C} (f : a ⟶ c) 
  (b : subobject c) [has_pullback f b.hom] : subobject a :=
subobject.mk (pullback f b.hom) (pullback_homo_l f b.hom) 
                                (mono_is_stable f b.hom b.is_mono)

def pullback_subobject_hom  {C : Category} {a c : C} (f : a ⟶ c) 
  {b₁ b₂ : subobject c} [has_pullback f b₁.hom] [has_pullback f b₂.hom] 
  (i : b₁ ⟶ b₂) : pullback_subobject f b₁ ⟶ pullback_subobject f b₂ :=
begin
  have w : (pullback_subobject f b₁).hom ≫ f = 
                              (pullback_homo_t f b₁.hom ≫ i.hom_obj) ≫ b₂.hom, from 
    begin 
      change pullback_homo_l f b₁.hom ≫ f = _, rwr pullback_eq, 
      rwr is_precat.assoc, rwr i.fac 
    end, 
  fapply hom_of_monos.mk, 
  { exact pullback_lift (square.of_i_j w) }, 
  { exact pb_lift_eq_l (square.of_i_j w) } 
end   

@[hott]
def subobj_intersect {C : Category} {c : C} (a b : subobject c) 
  [has_pullback a.hom b.hom] : subobject c :=
subobj_trans a (pullback_subobject a.hom b)  

@[hott, instance]
def subobj_has_inter {C : Category} {c : C} [has_pullbacks C] :
  has_inter (subobject c) :=
has_inter.mk (λ a b, subobj_intersect a b) 

@[hott]
def subobj_inter_symm {C : Category} {c : C} [has_pullbacks C]
  (a b : subobject c) : a ∩ b = b ∩ a :=
begin 
  fapply subobject_eq, 
  { exact sym_pullback_eq },
  { apply pathover_of_tr_eq, rwr <- category.idtoiso_linv sym_pullback_eq, 
    rwr iso_hom_tr_comp, apply eq.inverse, apply iso_move_lr, 
    change _ ≫ pullback_homo_l b.hom a.hom ≫ _ = pullback_homo_l a.hom b.hom ≫ _, 
    rwr pullback_eq a.hom b.hom, rwr <- is_precat.assoc, rwr sym_pullback_legs_eq }
end  

@[hott]
def pb_subobj_functor {C : Category} {a c : C} (f : a ⟶ c) 
  [has_pullbacks C] : subobject c ⥤ subobject a :=
precategories.functor.mk (λ b : subobject c, pullback_subobject f b)
                      (λ b₁ b₂ i, pullback_subobject_hom f i)
                      (λ b, is_prop.elim _ _)
                      (λ b₁ b₂ b₃ i₁ i₂, is_prop.elim _ _) 


/- The pullback functor of subobjects has adjoints if the category has images stable
   under pullbacks. -/
@[hott]
def image_is_stable {C : Category} {a b c : C} (f : a ⟶ c) (g : b ⟶ c)
  [has_images C] [has_pullbacks C] := 
  hom.image (pullback_homo_l f g) = pullback_subobject f (hom.image g) 

@[hott]
class has_stable_images (C : Category) :=
  (has_im : has_images C)
  (has_pb : has_pullbacks C)
  (stable_im : Π (a b c : C) (f : a ⟶ c) (g : b ⟶ c), image_is_stable f g)

@[hott, instance]
def has_images_of_has_stable_images (C : Category)
  [H : has_stable_images C] : has_images C := H.has_im

@[hott, instance]
def has_pullbacks_of_has_stable_images (C : Category) 
  [H : has_stable_images C] : has_pullbacks C := H.has_pb


/- The existence of a left adjoint to the pullback functor for subobjects can be deduced
   from the existence of pullbacks and the stability of images under puillbacks -/
@[hott]
class has_ex_in_fiber {C : Category} [has_pullbacks C] 
  {a b : C} (f : a ⟶ b) := 
(ex_in : has_left_adjoint (pb_subobj_functor f))  

@[hott, instance]
def has_l_adj_of_has_ex_fib {C : Category} [has_pullbacks C] 
  {a b : C} (f : a ⟶ b) [H : has_ex_in_fiber f] : 
  has_left_adjoint (pb_subobj_functor f) :=
H.ex_in

@[hott]
def ex_fib {C : Category} [has_pullbacks C] {a b : C} 
  (f : a ⟶ b) [has_ex_in_fiber f] : subobject a ⥤ subobject b :=
left_adjoint_of (pb_subobj_functor f) 

@[hott]
class has_ex_in_fibers (C : Category) :=
  (has_pb : has_pullbacks C)
  (has_ex_fib : Π {a b : C} (f : a ⟶ b), has_ex_in_fiber f)

@[hott, instance]
def has_pullbacks_of_has_ex_fibs {C : Category} [has_ex_in_fibers C] :
  has_pullbacks C := has_ex_in_fibers.has_pb C

@[hott, instance]
def has_ex_fib_of_has_ex_fibs {C : Category} [has_ex_in_fibers C]
  {a b : C} (f : a ⟶ b) : has_ex_in_fiber f := 
has_ex_in_fibers.has_ex_fib f

@[hott]
def ex_fib_of_stable_im {C : Category} [has_stable_images C] {a b : C} 
  (f : a ⟶ b) : subobject a ⥤ subobject b :=
begin 
  fapply precategories.functor.mk, 
  { exact λ c : subobject a, @hom.image C c.obj b (c.hom ≫ f) _ },
  { intros c d i, 
    have H : hom.image (c.hom ≫ f) = @hom.image C c.obj _ (i.hom_obj ≫ d.hom ≫ f) _, from
      ap (λ h : c.obj ⟶ a, hom.image (h ≫ f)) i.fac⁻¹ ⬝ 
                                    ap (λ h, hom.image h) (is_precat.assoc _ _ _),
    exact H⁻¹ ▸[λ e : subobject b, e ⟶ @hom.image _ d.obj _ (d.hom ≫ f) _] 
                                                   im_incl i.hom_obj (d.hom ≫ f) },
  { exact λ c, is_prop.elim _ _ },
  { exact λ c₁ c₂ c₃ i₁ i₂, is_prop.elim _ _ }
end  

@[hott]
def fib_ex_left_adj_pb_subobj {C : Category} [has_stable_images C] 
  {a b : C} (f : a ⟶ b) : 
  adjoint_functors (ex_fib_of_stable_im f) (pb_subobj_functor f) :=
begin
  apply adjoint_hom_to_adjoint, fapply adjoint_functors_on_hom.mk, 
  { intros c d, fapply has_inverse_to_bijection,
    { intro i, fapply hom_of_monos.mk, 
      { have w : c.hom ≫ f = (@hom_to_image _ c.obj _ (c.hom ≫ f) _ ≫ i.hom_obj) ≫ d.hom, from 
          begin 
            apply eq.concat (hom_to_image_eq (c.hom ≫ f))⁻¹, rwr is_precat.assoc, 
            exact ap (λ h : (hom.image (c.hom ≫ f)).obj ⟶ b, 
                                             hom_to_image (c.hom ≫ f) ≫ h) i.fac⁻¹         
          end,
        exact pullback_lift (square.of_i_j w) }, 
      { change pullback_lift _ ≫ pullback_homo_l _ _ = _, rwr pb_lift_eq_l } },
    { intro j, fapply hom_image_univ (c.hom ≫ f) d (j.hom_obj ≫ (pullback_homo_t _ _)), 
      rwr is_precat.assoc, rwr <- pullback_eq, rwr <- is_precat.assoc, 
      change (_ ≫ ((pb_subobj_functor f).obj d).hom) ≫ _ = _, rwr j.fac },
    { fapply is_set_inverse_of.mk, all_goals { intro h, exact is_prop.elim _ _ } } },
  { intros _ _ _ _ _, exact is_prop.elim _ _ },
  { intros _ _ _ _ _, exact is_prop.elim _ _ }
end  

@[hott, instance]
def has_ex_fibs_of_has_stable_ims {C : Category} [has_stable_images C] :
  has_ex_in_fibers C :=
has_ex_in_fibers.mk (has_pullbacks_of_has_stable_images C) 
  (λ a b f, has_ex_in_fiber.mk (has_left_adjoint.mk 
        (is_right_adjoint.mk (ex_fib_of_stable_im f) (fib_ex_left_adj_pb_subobj f))))
                                                

/- The existence of a right adjoint to the pullback functor for subobjects must be 
   assumed independently of other categorical properties. -/
@[hott]
class has_all_of_fiber {C : Category} [has_pullbacks C] 
  {a b : C} (f : a ⟶ b) := 
(fib_all : has_right_adjoint (pb_subobj_functor f))  

@[hott, instance]
def has_r_adj_of_has_all_fib {C : Category} [has_pullbacks C] 
  {a b : C} (f : a ⟶ b) [H : has_all_of_fiber f] : 
  has_right_adjoint (pb_subobj_functor f) :=
H.fib_all

@[hott]
def fib_all {C : Category} [has_pullbacks C] {a b : C} 
  (f : a ⟶ b) [has_all_of_fiber f] : subobject a ⥤ subobject b :=
right_adjoint_of (pb_subobj_functor f) 

@[hott]
class has_all_of_fibers (C : Category) :=
  (has_pb : has_pullbacks C)
  (has_all_fib : Π {a b : C} (f : a ⟶ b), has_all_of_fiber f)

@[hott, instance]
def has_pullbacks_of_has_all_fibs {C : Category} [has_all_of_fibers C] :
  has_pullbacks C := has_all_of_fibers.has_pb C

@[hott, instance]
def has_all_fib_of_has_all_fibs {C : Category} [has_all_of_fibers C]
  {a b : C} (f : a ⟶ b) : has_all_of_fiber f := 
has_all_of_fibers.has_all_fib f     

/- The fiberwise forall quantifier allows to define implications of subobjects. -/
@[hott]
structure implication {C : Category} {c : C} [has_pullbacks C] 
  (a b : subobject c) :=
  (impl : subobject c)
  (cond : impl ∩ a ⟶ b)
  (max : ∀ d : subobject c, (d ∩ a ⟶ b) -> (d ⟶ impl))

@[hott]
class has_implication {C : Category} {c : C} (a b : subobject c) := 
  (has_pb : has_pullbacks C)
  (has_impl : implication a b)

@[hott, instance]
def has_pb_of_has_impl {C : Category} {c : C} (a b : subobject c) 
  [H : has_implication a b] : has_pullbacks C :=
H.has_pb  

@[hott] 
def impl_subobj {C : Category} {c : C} (a b : subobject c) 
  [H : has_implication a b] : subobject c :=
H.has_impl.impl     

infixl ` ⇒ `:10 := impl_subobj 

@[hott]
def implications_of_all_fibs {C : Category} {c : C} 
  [has_all_of_fibers C] (a b : subobject c) : implication a b :=
begin
  fapply implication.mk,
  { exact (fib_all a.hom).obj (pullback_subobject a.hom b) },
  { sorry },
  { sorry }
end    

@[hott, instance]
def has_impl_of_all_fibs {C : Category} {c : C} 
  [has_all_of_fibers C] (a b : subobject c) : has_implication a b :=
has_implication.mk _ (implications_of_all_fibs a b)  

end categories.pullbacks

end hott     