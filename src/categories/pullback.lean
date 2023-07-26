import categories.limits categories.adjoints

universes v v' u u' w
hott_theory

namespace hott
open hott.precategories hott.categories hott.categories.limits hott.is_trunc 
     categories.adjoints hott.set hott.subset hott.trunc 

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

@[hott, instance]
def has_pbs_is_prop (C : Type _) [is_cat C] : is_prop (has_pullbacks C) :=
begin 
  apply is_prop.mk, intros hpbs₁ hpbs₂, hinduction hpbs₁, hinduction hpbs₂,
  apply ap has_pullbacks.mk, exact is_prop.elim _ _ 
end

@[hott, instance]
def has_pullback_of_has_pullbacks {C : Type _} [is_cat C] 
  [has_pullbacks C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : has_pullback f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_pullbacks.has_limit_of_shape C) (orthogonal_pair f g)⟩

@[hott, instance]
def has_pullback_of_has_limits_of_shape {C : Type _} [is_cat C] 
  [H : has_limits_of_shape orthogonal_wedge C] {a b c : C} (f : a ⟶ c) (g : b ⟶ c) : 
  has_pullback f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ H (orthogonal_pair f g)⟩ 

@[hott, instance]
def has_pullbacks_of_has_limits (C : Category) [H : has_limits C] : 
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
((get_limit_cone (orthogonal_pair f g)).is_limit.lift S).v_lift 

@[hott]
def pb_lift_eq_l {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : 
  pullback_lift S ≫ pullback_homo_l f g = square_left S :=
((get_limit_cone (orthogonal_pair f g)).is_limit.lift S).fac ow_left  

@[hott]
def pb_lift_eq_t {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  (S : square f g) [has_pullback f g] : 
  pullback_lift S ≫ pullback_homo_t f g = square_top S :=
((get_limit_cone (orthogonal_pair f g)).is_limit.lift S).fac ow_upper  

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
(get_limit_cone (orthogonal_pair f g)).is_limit.uniq S (cone_map.mk h w) 

@[hott]
def pullback_lift_eq {C : Type _} [is_cat C] {a b c d : C} {f : a ⟶ c} {g : b ⟶ c}
  [has_pullback f g] : Π (h h' : d ⟶ pullback f g),
  h ≫ pullback_homo_l f g = h' ≫ pullback_homo_l f g ->
  h ≫ pullback_homo_t f g = h' ≫ pullback_homo_t f g -> h = h' :=
begin
  intros h h' pl pt, 
  have q : (h ≫ pullback_homo_l f g) ≫ f = (h ≫ pullback_homo_t f g) ≫ g, from 
    begin rwr is_precat.assoc, rwr pullback_eq, rwr is_precat.assoc end,
  have r : h = pullback_lift (square.of_i_j q), from 
    begin fapply pullback_uniq (square.of_i_j q), refl, refl end,
  rwr r, apply eq.inverse, fapply pullback_uniq (square.of_i_j q), rwr <- pl, rwr <- pt
end

@[hott]
def pullback_uniq_id {C : Type _} [is_cat C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  [has_pullback f g] : Π (h : pullback f g ⟶ pullback f g),
  h ≫ pullback_homo_l f g = pullback_homo_l f g -> 
  h ≫ pullback_homo_t f g = pullback_homo_t f g -> h = 𝟙 (pullback f g) :=
begin 
  intros h pl pt, fapply pullback_lift_eq h (𝟙 (pullback f g)), 
  { rwr pl, rwr is_precat.id_comp }, 
  { rwr pt, rwr is_precat.id_comp } 
end

@[hott]
def pullback_trans {C : Category} {a b c d : C} (f : a ⟶ b) (g : b ⟶ c)
  (h : d ⟶ c) [has_pullback g h] [has_pullback (f ≫ g) h] 
  [has_pullback f (pullback_homo_l g h)] :
  pullback f (pullback_homo_l g h) = pullback (f ≫ g) h :=
begin
  have p : pullback_homo_l f (pullback_homo_l g h) ≫ f ≫ g =
             (pullback_homo_t f (pullback_homo_l g h) ≫ (pullback_homo_t g h)) ≫ h, from
    begin 
      rwr <- is_precat.assoc, rwr pullback_eq, rwr is_precat.assoc, rwr pullback_eq, 
      rwr is_precat.assoc 
    end,
  have q : (pullback_homo_l (f ≫ g) h ≫ f) ≫ g = pullback_homo_t (f ≫ g) h ≫ h, from
    begin rwr is_precat.assoc, rwr pullback_eq end,
  have r : pullback_homo_l (f ≫ g) h ≫ f = (@pullback_lift _ _ _ _ _ g h 
             (square.of_i_j q) _) ≫ pullback_homo_l g h, by rwr pb_lift_eq_l,
  apply @category.isotoid, fapply iso.mk,
  { exact pullback_lift (square.of_i_j p) },
  { fapply is_iso.mk, 
    { exact pullback_lift (square.of_i_j r) },
    { apply pullback_uniq_id, 
      { rwr is_precat.assoc, rwr pb_lift_eq_l, 
        change pullback_lift _ ≫ pullback_homo_l _ _ = _, rwr pb_lift_eq_l },
      { rwr is_precat.assoc, rwr pb_lift_eq_t, 
        change pullback_lift _ ≫ pullback_homo_t _ _ ≫ pullback_homo_t _ _ = _, 
        rwr <- is_precat.assoc, rwr pb_lift_eq_t, 
        change pullback_lift _ ≫ _ = _, rwr pb_lift_eq_t } },
    { apply pullback_uniq_id,
      { rwr is_precat.assoc, rwr pb_lift_eq_l, 
        change pullback_lift _ ≫ pullback_homo_l _ _ = _, rwr pb_lift_eq_l },
      { rwr is_precat.assoc, rwr pb_lift_eq_t, 
        change pullback_lift _ ≫ (@pullback_lift _ _ _ _ _ g h (square.of_i_j q) _) = _, 
        apply pullback_lift_eq, 
        { rwr is_precat.assoc, rwr pb_lift_eq_l, change _ ≫ _ ≫ _ = _, 
          rwr <- is_precat.assoc, rwr pb_lift_eq_l, change pullback_homo_l _ _ ≫ _ = _,
          rwr pullback_eq },
        { rwr is_precat.assoc, rwr pb_lift_eq_t, change _ ≫ pullback_homo_t _ _ = _, 
          rwr pb_lift_eq_t } } } }
end

@[hott]
def pullback_trans_left_legs {C : Category} {a b c d : C} (f : a ⟶ b) (g : b ⟶ c)
  (h : d ⟶ c) [has_pullback g h] [has_pullback (f ≫ g) h] 
  [has_pullback f (pullback_homo_l g h)] :
  pullback_homo_l f (pullback_homo_l g h) = 
                (idtoiso (pullback_trans f g h)).hom ≫ (pullback_homo_l (f ≫ g) h) :=
begin
  change _ = (idtoiso (idtoiso⁻¹ᶠ _)).hom ≫ _, rwr category.idtoiso_rinv, 
  rwr pb_lift_eq_l
end


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
  exact @diag_iso_has_lim_to_has_lim.{v u 0 0 0 0} _ _ _ _ orthogonal_wedge_iso _
        pull_fg.has_limit        
end

@[hott]
def sym_pullback_eq {C : Type u} [is_cat.{v} C] {a b c : C} {f : a ⟶ c} {g : b ⟶ c}
  [has_pullback.{u v} f g] [has_pullback.{u v} g f] : pullback f g = pullback g f :=
begin
  change limit _ = limit _,
  exact (diag_iso_lim_eq_lim.{v u 0 0 0 0} orthogonal_wedge_iso (orthogonal_pair f g))⁻¹ ⬝ 
        (@diag_eq_lim_eq_lim Orthogonal_Wedge C _ _ (orthogonal_pair g f) 
          (eq.inverse (sym_orthogonal_pair f g)) 
          (diag_iso_has_lim_to_has_lim.{v u 0 0 0 0} orthogonal_wedge_iso) _)
end

@[hott]
def sym_pullback_legs_eq {C : Type u} [is_cat.{v} C] {a b c : C} (f : a ⟶ c) 
  (g : b ⟶ c) [has_pullback.{u v} f g] [has_pullback.{u v} g f] : 
  (idtoiso sym_pullback_eq).hom ≫ pullback_homo_l g f = pullback_homo_t f g :=
begin
  change (idtoiso (_ ⬝ _)).hom ≫ _ = _, rwr <- idtoiso_comp_eq, rwr is_precat.assoc, 
  rwr id_inv_iso_inv, apply eq.inverse, apply iso_move_lr, 
  change _ ≫ limit_leg _ (orthogonal_wedge_iso.hom.obj (inf_w_node.tip ow_node.left)) = _,
  rwr diag_iso_lim_legs_eq, rwr diag_inv_eq_lim_eq, rwr id_inv_iso_inv,
  rwr <- id_hom_tr_comp, 
  rwr @diag_eq_leg_eq Orthogonal_Wedge C _ (orthogonal_pair g f) _ (sym_orthogonal_pair f g),
  have r : ap (λ (F : Orthogonal_Wedge.obj ⥤ C), F.obj (inf_w_node.tip ow_node.left)) 
           (sym_orthogonal_pair f g) = idp, from 
  begin 
    rwr ap_compose (λ (h : Orthogonal_Wedge.obj -> C), h (inf_w_node.tip ow_node.left)) 
        functor.obj, 
    change ap _ (ap _ (functor_eq _ _)) = _, rwr functor_eq_obj, change ap10 _ _ = _,
    rwr ap10_eq_of_homotopy 
  end,
  rwr r
end

/- The stability of monomorphisms under pullbacks can be used to construct pullbacks 
   of subobjects and hence their intersection. -/
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
  (i : b₁ ≼ b₂) : pullback_subobject f b₁ ≼ pullback_subobject f b₂ :=
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
def pb_subobj_functor {C : Category} {a c : C} (f : a ⟶ c) 
  [has_pullbacks C] : subobject c ⥤ subobject a :=
precategories.functor.mk (λ b : subobject c, pullback_subobject f b)
                      (λ b₁ b₂ i, pullback_subobject_hom f i)
                      (λ b, is_prop.elim _ _)
                      (λ b₁ b₂ b₃ i₁ i₂, is_prop.elim _ _) 

@[hott]
def pb_subobj_lift {C : Category} {c c' : C} (f : c' ⟶ c) (a : subobject c)  
  (b : subobject c') [has_pullbacks C] : Π (h : b.obj ⟶ a.obj), 
  (b.hom ≫ f = h ≫ a.hom) -> (b ≼ pullback_subobject f a) :=
begin
  intros h ph,
  let S : square f a.hom := square.of_i_j ph, 
  fapply hom_of_monos.mk,
  { exact (pullback_lift S) },
  { change _ ≫ pullback_homo_l f a.hom = _, rwr pb_lift_eq_l }
end  

@[hott]
def subobj_pullback_trans {C : Category} {c : C} (a : subobject c)  
  (b : subobject a.obj) [has_pullbacks C] :
  pullback_subobject a.hom (subobj_subobj_trans a b) = b :=
begin
  fapply subobj_antisymm,
  { fapply hom_of_monos.mk,
    { exact pullback_homo_t a.hom _ },
    { apply a.is_mono, change _ = pullback_homo_l _ _ ≫ _,
      rwr pullback_eq, rwr is_precat.assoc } },
  { apply pb_subobj_lift a.hom (subobj_subobj_trans a b) b (𝟙 b.obj),
    rwr is_precat.id_comp }
end

/- We introduce the structure of a subobject classifier and the class of categories with
   such a structure. -/
@[hott]
structure subobject_classifier (C : Category) [has_pullbacks C] [has_terminal C] :=
  (truth_val : C)
  (true : terminal_obj C ⟶ truth_val)
  (class_map : Π {c : C} (b : subobject c), c ⟶ truth_val)
  (cart : Π {c : C} (b : subobject c), b = pullback_subobject (class_map b) 
                                                              (term_subobj true))
  (uniq : Π {c : C} (b : subobject c) (cl : c ⟶ truth_val),  
            b = pullback_subobject cl (term_subobj true) -> cl = class_map b)

@[hott]
class has_so_classifier (C : Category) [has_pullbacks C] [has_terminal C] :=
  (so_class : subobject_classifier C)


/- The intersection of two subobjects and some of its properties. -/
@[hott]
def subobj_intersect {C : Category} {c : C} (a b : subobject c) 
  [has_pullback a.hom b.hom] : subobject c :=
subobj_subobj_trans a (pullback_subobject a.hom b)  

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
def subobj_inter_linc {C : Category} {c : C} [has_pullbacks C]
  (a b : subobject c) : a ∩ b ≼ a :=
begin
  fapply hom_of_monos.mk, 
  { exact (pullback_subobject a.hom b).hom },
  { refl }
end

@[hott]
def subobj_inter_rinc {C : Category} {c : C} [has_pullbacks C]
  (a b : subobject c) : a ∩ b ≼ b :=
begin
  fapply hom_of_monos.mk, 
  { exact pullback_homo_t a.hom b.hom },
  { exact (pullback_eq a.hom b.hom)⁻¹ }
end

@[hott]
def subobj_inter_lift {C : Category} {d : C} [has_pullbacks C]
  {a b c : subobject d} : (c ≼ a) -> (c ≼ b) -> (c ≼ a ∩ b) :=
begin
  intros ca cb, fapply hom_of_monos.mk,
  { let S : square a.hom b.hom := square.of_i_j (ca.fac ⬝ cb.fac⁻¹), 
    exact pullback_lift S },
  { change _ ≫ pullback_homo_l _ _ ≫ a.hom = _, rwr <- is_precat.assoc,
    rwr pb_lift_eq_l, change ca.hom_obj ≫ _ = _, rwr ca.fac } 
end

@[hott]
def subobj_hom_inter_absorb {C : Category} {c : C} [has_pullbacks C] {a b : subobject c} : 
  a ≼ b -> a ∩ b = a :=
begin
  intro ineq, fapply subobj_antisymm,
  { exact subobj_inter_linc _ _ },
  { fapply subobj_inter_lift, exact 𝟙 a, exact ineq }
end 

@[hott]
def top_inter_absorb {C : Category} {c : C} [has_pullbacks C] (a : subobject c) : 
  a ∩ (top_subobject c) = a :=
subobj_hom_inter_absorb (top_subobj_prop a)

@[hott]
def subobj_inter_assoc {C : Category} {d : C} [has_pullbacks C] : Π {a b c : subobject d},
  (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
begin 
  intros a b c, fapply subobj_antisymm,
  { fapply subobj_inter_lift,
    { exact subobj_trans (subobj_inter_linc (a ∩ b) c) (subobj_inter_linc a b) },
    { fapply subobj_inter_lift,
      { exact subobj_trans (subobj_inter_linc (a ∩ b) c) (subobj_inter_rinc a b) },
      { exact subobj_inter_rinc _ _ } } },
  { fapply subobj_inter_lift,
    { fapply subobj_inter_lift,
      { exact subobj_inter_linc _ _ },
      { exact subobj_trans (subobj_inter_rinc a (b ∩ c)) (subobj_inter_linc b c) } },
    { exact subobj_trans (subobj_inter_rinc a (b ∩ c)) (subobj_inter_rinc b c) } }
end 

@[hott]
def subobj_inter_hom_of_pb_hom {C : Category} {d : C} [has_pullbacks C]
  (a b c : subobject d) : 
  (pullback_subobject a.hom b ≼ pullback_subobject a.hom c) -> (a ∩ b ≼ a ∩ c) :=
begin
  intro pb_hom, fapply hom_of_monos.mk,
  { exact pb_hom.hom_obj },
  { change _ ≫ _ ≫ a.hom = _ ≫ a.hom, rwr <- is_precat.assoc, rwr pb_hom.fac }
end

@[hott]
def pb_hom_of_subobj_inter_hom {C : Category} {d : C} [has_pullbacks C]
  {a b c : subobject d} : 
  (a ∩ b ≼ a ∩ c) -> (pullback_subobject a.hom b ≼ pullback_subobject a.hom c) :=
begin
  intro soi_hom, fapply hom_of_monos.mk,
  { exact soi_hom.hom_obj },
  { apply a.is_mono, rwr is_precat.assoc, change _ ≫ (a ∩ c).hom = (a ∩ b).hom, 
    rwr soi_hom.fac }
end

@[hott]
def pullback_inter_eq {C : Category} {c c' : C} (f : c' ⟶ c) [has_pullbacks C]
  (a b : subobject c) : 
  (pullback_subobject f (a ∩ b)) = ((pullback_subobject f a) ∩ (pullback_subobject f b)) :=
begin
  have p : ((subobj_inter_linc (pullback_subobject f a) (pullback_subobject f b)).hom_obj ≫
            pullback_homo_t f a.hom) ≫ a.hom = 
           ((subobj_inter_rinc (pullback_subobject f a) (pullback_subobject f b)).hom_obj ≫
            pullback_homo_t f b.hom) ≫ b.hom, from 
  begin 
    rwr is_precat.assoc, rwr is_precat.assoc, 
    rwr <- pullback_eq, rwr <- pullback_eq,
    rwr <- is_precat.assoc, rwr <- is_precat.assoc, 
    change (pullback_homo_l (pullback_homo_l f a.hom) (pullback_homo_l f b.hom) ≫ _) ≫ _ = _,
    rwr pullback_eq 
  end,
  let S := square.of_i_j p, 
  apply subobj_antisymm,
  { apply subobj_inter_lift _ _, 
    { exact pullback_subobject_hom f (subobj_inter_linc a b) },
    { exact pullback_subobject_hom f (subobj_inter_rinc a b) } },
  { fapply pb_subobj_lift f _ _,
    { exact pullback_lift S },
    { change _ = _ ≫ (pullback_homo_l a.hom b.hom) ≫ a.hom, 
      rwr <- is_precat.assoc, rwr pb_lift_eq_l, 
      change _ = (_ ≫ _) ≫ _, rwr is_precat.assoc, rwr <- pullback_eq, 
      rwr <- is_precat.assoc } }
end


/- The pullback functor of subobjects has adjoints if the category has images stable
   under pullbacks. 
   
   We avoid different routes to instances of pullbacks by not extending from 
   `has_pullbacks` and introducing a class combining pullbacks and stable images,
   so that we can use `has_stable_image` without providing `has_pullbacks` in models. -/
@[hott]
class has_stable_images (C : Category) [has_pullbacks C] extends has_images C  :=
  (stable_im : Π {a b c : C} (f : a ⟶ c) (g : b ⟶ c), 
                  hom.image (pullback_homo_l f g) = pullback_subobject f (hom.image g))

@[hott, instance]
def has_stab_im_is_prop (C : Category) [has_pullbacks C] : is_prop (has_stable_images C) :=
begin 
  apply is_prop.mk, intros hsi₁ hsi₂, hinduction hsi₁, hinduction hsi₂,
  fapply apd011 (@has_stable_images.mk _ _), exact is_prop.elim _ _,
  apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end

@[hott]
class has_pb_and_stab_im (C : Category) :=
  (pb_stab_im : Σ (H : has_pullbacks C), has_stable_images C)

@[hott, instance]
def has_pb_stab_im_is_prop (C : Category) [has_pullbacks C] : 
  is_prop (has_pb_and_stab_im C) :=
begin 
  apply is_prop.mk, intros hpsi₁ hpsi₂, hinduction hpsi₁, hinduction hpsi₂,
  apply ap has_pb_and_stab_im.mk, exact is_prop.elim _ _
end


/- The existence of a left adjoint to the pullback functor for subobjects can be deduced
   from the existence of pullbacks and the stability of images under pullbacks -/
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
def ex_fib_left_adj {C : Category} [has_pullbacks C] {a b : C} 
  (f : a ⟶ b) [has_ex_in_fiber f] (c : subobject a) (d : subobject b) : 
  (c ≼ pullback_subobject f d) -> ((ex_fib f).obj c ⟶ d) :=
begin 
  let H' : has_left_adjoint (pb_subobj_functor f) := by apply_instance,
  have p : ex_fib f = H'.r_adj.L, from rfl, rwr p, 
  apply @right_adj_hom _ _ _ _ _ _ (@is_adj_of_has_left_adj _ _ _ _ _ H')
end 

@[hott]
def ex_fib_right_adj {C : Category} [has_pullbacks C] {a b : C} 
  (f : a ⟶ b) [has_ex_in_fiber f] (c : subobject a) (d : subobject b) : 
  ((ex_fib f).obj c ⟶ d) -> (c ≼ pullback_subobject f d) :=
begin 
  let H' : has_left_adjoint (pb_subobj_functor f) := by apply_instance,
  have p : ex_fib f = H'.r_adj.L, from rfl, rwr p, 
  apply @left_adj_hom _ _ _ _ _ _ (@is_adj_of_has_left_adj _ _ _ _ _ H')
end 

@[hott]
class has_ex_in_fibers (C : Category) [has_pullbacks C] :=
  (has_ex_fib : Π {a b : C} (f : a ⟶ b), has_ex_in_fiber f)

@[hott, instance]
def has_ex_fib_of_has_ex_fibs {C : Category} [has_pullbacks C] [has_ex_in_fibers C]
  {a b : C} (f : a ⟶ b) : has_ex_in_fiber f := 
has_ex_in_fibers.has_ex_fib f

@[hott]
def ex_fib_of_stable_im {C : Category} [has_pullbacks C] 
  [has_stable_images C] {a b : C} (f : a ⟶ b) : subobject a ⥤ subobject b :=
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
def fib_ex_left_adj_pb_subobj {C : Category} [has_pullbacks C] [has_stable_images C] 
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
def has_ex_fibs_of_has_stable_ims {C : Category} [has_pullbacks C]
  [has_stable_images C] : has_ex_in_fibers C :=
has_ex_in_fibers.mk (λ a b f, has_ex_in_fiber.mk (has_left_adjoint.mk 
        (is_right_adjoint.mk (ex_fib_of_stable_im f) (fib_ex_left_adj_pb_subobj f))))

@[hott]
def ex_fib_inter {C : Category} [has_pullbacks C] [Hsi : has_stable_images C] {c c' : C}
  (f : c' ⟶ c) (a : subobject c) (b : subobject c') : 
  a ∩ (ex_fib_of_stable_im f).obj b = 
                      (ex_fib_of_stable_im f).obj ((pb_subobj_functor f).obj a ∩ b) :=
begin
  change _ = hom.image (((pullback_homo_l (pullback_homo_l f a.hom) b.hom) ≫ 
                                                   (pullback_homo_l f a.hom)) ≫ f),
  rwr pullback_eq, rwr is_precat.assoc,  
  rwr <- sym_pullback_legs_eq (pullback_homo_l f a.hom) b.hom, rwr is_precat.assoc,
  rwr im_iso_comp (idtoiso sym_pullback_eq) 
                    (pullback_homo_l b.hom (pullback_homo_l f a.hom) ≫ b.hom ≫ f), 
  rwr pullback_trans_left_legs b.hom f a.hom, rwr is_precat.assoc,
  rwr im_iso_comp (idtoiso (pullback_trans b.hom f a.hom)) 
                  (pullback_homo_l (b.hom ≫ f) a.hom ≫ b.hom ≫ f),
  rwr pullback_eq, change subobj_subobj_trans a _ = _, 
  apply λ p, p ⬝ (im_incl_eq a (pullback_homo_t (b.hom ≫ f) a.hom))⁻¹,
  apply ap (subobj_subobj_trans a), 
  let p := @sym_pullback_legs_eq _ _ _ _ _ (b.hom ≫ f) a.hom _ _, rwr <- p,
  rwr im_iso_comp (idtoiso sym_pullback_eq) (pullback_homo_l a.hom (b.hom ≫ f)),
  rwr @has_stable_images.stable_im _ _ Hsi _ _ _ _ _
end

@[hott]
def stable_top {C : Category} [has_pullbacks C] [has_ex_in_fibers C] {a b : C} 
  (f : a ⟶ b) : pullback_subobject f (top_subobject b) = top_subobject a :=
begin apply top_subobj_unique, intro c, apply ex_fib_right_adj, apply top_subobj_prop end 


/- The existence of a right adjoint to the pullback functor for subobjects must be 
   assumed independently of other categorical properties. -/
@[hott]
class has_all_of_fiber {C : Category} [has_pullbacks C] 
  {a b : C} (f : a ⟶ b) := 
(fib_all : has_right_adjoint (pb_subobj_functor f))  

@[hott, instance]
def has_all_fib_is_prop (C : Category) [has_pullbacks C] {a b : C} (f : a ⟶ b) : 
  is_prop (has_all_of_fiber f) :=
begin 
  apply is_prop.mk, intros hpsi₁ hpsi₂, hinduction hpsi₁, hinduction hpsi₂,
  apply ap has_all_of_fiber.mk, exact is_prop.elim _ _
end

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
class has_all_of_fibers (C : Category) [has_pullbacks C] :=
  (has_all_fib : Π {a b : C} (f : a ⟶ b), has_all_of_fiber f)

@[hott, instance]
def has_all_fibs_is_prop (C : Category) [has_pullbacks C] : 
  is_prop (has_all_of_fibers C) :=
begin 
  apply is_prop.mk, intros hafs₁ hafs₂, hinduction hafs₁, hinduction hafs₂,
  apply ap has_all_of_fibers.mk, exact is_prop.elim _ _
end

@[hott, instance]
def has_all_fib_of_has_all_fibs {C : Category} [has_pullbacks C] [has_all_of_fibers C]
  {a b : C} (f : a ⟶ b) : has_all_of_fiber f := 
has_all_of_fibers.has_all_fib f  

@[hott]
class has_pb_and_all_fib (C : Category) :=
  (pb_all_fib : Σ (H : has_pullbacks C), has_all_of_fibers C) 

@[hott, instance]
def has_pb_fibs_is_prop (C : Category) [has_pullbacks C] : 
  is_prop (has_pb_and_all_fib C) :=
begin 
  apply is_prop.mk, intros hafs₁ hafs₂, hinduction hafs₁, hinduction hafs₂,
  apply ap has_pb_and_all_fib.mk, exact is_prop.elim _ _
end

/- The fiberwise forall quantifier allows to define implications of subobjects. -/
@[hott]
structure implication {C : Category} {c : C} [has_pullbacks C] (a b : subobject c) :=
  (impl : subobject c)
  (cond : a ∩ impl ≼ b)
  (max : ∀ d : subobject c, (a ∩ d ≼ b) -> (d ≼ impl))

@[hott]
def implication_is_unique {C : Category} {c : C} [has_pullbacks C] {a b : subobject c}
  (imp₁ imp₂ : implication a b) : imp₁.impl = imp₂.impl :=
begin
  apply subobj_antisymm imp₁.impl imp₂.impl, 
  { exact imp₂.max imp₁.impl imp₁.cond },
  { exact imp₁.max imp₂.impl imp₂.cond }
end

@[hott]
class has_implication {C : Category} [has_pullbacks C] {c : C} (a b : subobject c) := 
  (has_impl : implication a b)

@[hott] 
def impl_subobj {C : Category} [has_pullbacks C] {c : C} (a b : subobject c) 
  [H : has_implication a b] : subobject c :=
H.has_impl.impl     

infixl ` ⇒ `:10 := impl_subobj 

@[hott]
def implications_of_all_fibs {C : Category} {c : C} [has_pullbacks C]
  [has_all_of_fibers C] (a b : subobject c) : implication a b :=
begin
  fapply implication.mk,
  { exact (fib_all a.hom).obj (pullback_subobject a.hom b) },
  { apply λ h : a ∩ (fib_all a.hom).obj (pullback_subobject a.hom b) ⟶ a ∩ b, 
            h ≫ subobj_inter_rinc a b,  
    apply subobj_inter_hom_of_pb_hom a _ b, 
    exact (inv_bijection_of ((adjoint_to_adjoint_hom (adjoint_right_adjoint_of 
                                                     (pb_subobj_functor a.hom))).hom_bij 
                             ((fib_all a.hom).obj (pullback_subobject a.hom b)) 
                             (pullback_subobject a.hom b))).map 
            (id_iso ((fib_all a.hom).obj (pullback_subobject a.hom b))).hom },
  { intros d adb, 
    apply ((adjoint_to_adjoint_hom (adjoint_right_adjoint_of 
                (pb_subobj_functor a.hom))).hom_bij d (pullback_subobject a.hom b)).map, 
    exact pb_hom_of_subobj_inter_hom (subobj_inter_lift (subobj_inter_linc a d) adb) }
end    

@[hott, instance]
def has_impl_of_all_fibs {C : Category} {c : C} [has_pullbacks C]
  [has_all_of_fibers C] (a b : subobject c) : has_implication a b :=
has_implication.mk (implications_of_all_fibs a b)  

/- Implications are stable under pullbacks if images are stable. -/
@[hott]
def implication_is_stable {C : Category} {c c' : C} (f : c' ⟶ c) (a b : subobject c) 
  [has_pullbacks C] [has_all_of_fibers C] :=
  pullback_subobject f (a ⇒ b) = ((pullback_subobject f a) ⇒ (pullback_subobject f b))

@[hott]
class has_stable_implications (C : Category) [has_pullbacks C] [has_all_of_fibers C] :=
  (has_stab_impl : Π {c c' : C} (f : c' ⟶ c) (a b : subobject c), 
                     implication_is_stable f a b)

@[hott, instance]
def stable_implications_of_stable_images (C : Category) [has_pullbacks C]
  [Hsi : has_stable_images C] [Hf : has_all_of_fibers C] : has_stable_implications C :=
begin
  fapply has_stable_implications.mk,
  { intros c c' f a b, 
    apply subobj_antisymm _ _, 
    { apply implication.max, rwr <- pullback_inter_eq, 
      apply pullback_subobject_hom, apply implication.cond },
    { apply ((adjoint_to_adjoint_hom (adjoint_left_adjoint_of 
              (pb_subobj_functor f))).hom_bij _ (a ⇒ b)).map,
      apply implication.max, change ↥(a ∩ (ex_fib_of_stable_im f).obj _ ⟶ b),
      rwr ex_fib_inter f a _,
      apply (inv_bijection_of (((adjoint_to_adjoint_hom (adjoint_left_adjoint_of 
                                        (pb_subobj_functor f))).hom_bij _ _))).map,   
      apply implication.cond } }
end

/- The Heyting property of a category -/
@[hott]
class has_Heyting (C : Category) [has_pullbacks C] :=
  (has_ex_fib : Π {a b : C} (f : a ⟶ b), has_ex_in_fiber f)
  (has_all_fib : Π {a b : C} (f : a ⟶ b), has_all_of_fiber f)

@[hott, instance]
def has_ex_fibs_of_Heyting (C : Category) [has_pullbacks C] [hH : has_Heyting C] : 
  has_ex_in_fibers C :=
has_ex_in_fibers.mk hH.has_ex_fib

@[hott, instance]
def has_all_fibs_of_Heyting (C : Category) [has_pullbacks C] [hH : has_Heyting C] : 
  has_all_of_fibers C :=
has_all_of_fibers.mk hH.has_all_fib

end categories.pullbacks

end hott     