import categories.limits 

universes v v' u u' w
hott_theory

namespace hott
open hott.precategories hott.categories hott.categories.limits hott.is_trunc 
     categories.adjoints hott.set hott.subset hott.trunc 

namespace categories.inf_pullbacks

/- We need a pullback constructions for diagrams in `C` consisting of the arbitrary many 
   morphisms with common codomain, that is, diagrams over `inf_wedge`. -/
@[hott, hsimp]
def orthogonal_tuple_obj {C : Type _} [is_cat C] {J : Set} 
  {f : J -> C} {c : C} (leg : Π j : J, f j ⟶ c) : inf_wedge J -> C :=
λ s, match s with
     | inf_w_node.tip j := f j
     | inf_w_node.base C := c
     end    

@[hott, hsimp]
def orthogonal_tuple_map {C : Type _} [is_cat C] {J : Set} 
  {f : J -> C} {c : C} (leg : Π j : J, f j ⟶ c) : Π {s t : inf_wedge J}, 
  (s ⟶ t) -> (orthogonal_tuple_obj leg s ⟶ orthogonal_tuple_obj leg t) :=
begin 
  intros s t, hinduction s with j, all_goals { hinduction t with k }, 
  { intro ar, hinduction ar, exact 𝟙 _ }, 
  { intro ar, exact leg j }, 
  { intro ar, hinduction ar }, 
  { intro ar, exact 𝟙 _ } 
end

@[hott, hsimp]
def orthogonal_tuple_map_id {C : Type _} [is_cat C] {J : Set} 
  {f : J -> C} {c : C} (leg : Π j : J, f j ⟶ c) : 
  Π s : inf_wedge J, orthogonal_tuple_map leg (𝟙 s) = 𝟙 (orthogonal_tuple_obj leg s) :=
begin intro s, hinduction s with j, refl, refl end

@[hott, hsimp]
def orthogonal_tuple_map_comp {C : Type _} [is_cat C] {J : Set} 
  {f : J -> C} {c : C} (leg : Π j : J, f j ⟶ c) : Π {s t u : inf_wedge J}
  (g : s ⟶ t) (h : t ⟶ u), orthogonal_tuple_map leg (g ≫ h) = 
                       orthogonal_tuple_map leg g ≫ orthogonal_tuple_map leg h :=
begin
  intros s t u g h, hinduction s with j, all_goals { hinduction t with k }, 
  all_goals { try { hinduction g, change orthogonal_tuple_map leg (𝟙 _ ≫ h) = _, 
    rwr is_precat.id_comp, change _ = orthogonal_tuple_map leg (𝟙 _) ≫ _, 
    rwr orthogonal_tuple_map_id, rwr is_precat.id_comp } }, 
  { hinduction u with l, all_goals { induction h }, 
    change orthogonal_tuple_map leg (_ ≫ 𝟙 _) = _, rwr is_precat.comp_id, 
    change _ = orthogonal_tuple_map leg _ ≫ 𝟙 _, rwr is_precat.comp_id }, 
  hinduction g
end 

@[hott]
def orthogonal_tuple {C : Type _} [is_cat C] {J : Set} 
  {f : J -> C} {c : C} (leg : Π j : J, f j ⟶ c) : inf_wedge J ⥤ C :=
precategories.functor.mk (orthogonal_tuple_obj leg) 
                           (@orthogonal_tuple_map _ _ _ _ _ leg) 
                           (orthogonal_tuple_map_id leg) 
                           (@orthogonal_tuple_map_comp _ _ _ _ _ leg)  

/- Classes and instances for pullbacks along arbitrary many homomorphisms. -/
@[hott]
class has_inf_pullback {C : Type _} [is_cat C] {J : Set} {f : J -> C} {c : C} 
  (leg : Π j : J, f j ⟶ c) := (has_limit : has_limit (orthogonal_tuple leg))

@[hott, instance]
def has_limit_of_has_inf_pb {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} {c : C} 
  (leg : Π j : J, f j ⟶ c) [H : has_inf_pullback leg] : 
  has_limit (orthogonal_tuple leg) := H.has_limit

@[hott]
def inf_pullback {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} {c : C} 
  (leg : Π j : J, f j ⟶ c) [H : has_inf_pullback leg] := limit (orthogonal_tuple leg) 

@[hott]
def inf_pullback_homo {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} {c : C} 
  (leg : Π j : J, f j ⟶ c) [has_inf_pullback leg] : Π j : J, inf_pullback leg ⟶ f j :=
assume j, limit_leg (orthogonal_tuple leg) (inf_w_node.tip j)  

@[hott]
def inf_pullback_diag {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} {c : C} 
  (leg : Π j : J, f j ⟶ c) [has_inf_pullback leg] : inf_pullback leg ⟶ c :=
limit_leg (orthogonal_tuple leg) inf_w_base

@[hott]
class has_inf_pullbacks (C : Type u) [is_cat.{v} C] := 
  (has_limit_of_shape : Π (A : Set), has_limits_of_shape (inf_wedge A) C)

@[hott, instance]
def has_inf_pb_of_has_inf_pullbacks {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} (leg : Π j : J, f j ⟶ c) [has_inf_pullbacks C] : has_inf_pullback leg := 
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_inf_pullbacks.has_limit_of_shape C J) (orthogonal_tuple leg)⟩

@[hott, instance]
def has_inf_pb_of_has_limits_of_shape {C : Type u} [is_cat.{v} C] {J : Set} {f : J -> C} 
  {c : C} (leg : Π j : J, f j ⟶ c) [H : has_limits_of_shape (inf_wedge J) C] : 
  has_inf_pullback leg :=
⟨@has_limits_of_shape.has_limit _ _ _ _ H (orthogonal_tuple leg)⟩ 

@[hott, instance]
def has_inf_pullbacks_of_has_limits (C : Type u) [is_cat.{v} C] [H : has_limits C] : 
  has_inf_pullbacks C :=
has_inf_pullbacks.mk (λ J, @has_limits.has_limit_of_shape C _ H (inf_wedge J) _) 

/- The cone over an `orthogonal_tuple` is a `hsquare` (for hypersquare). -/
@[hott]
abbreviation hsquare {C : Type _} [is_cat C] {J : Set} {f : J -> C} 
  {c : C} (leg : Π j : J, f j ⟶ c) := cone (orthogonal_tuple leg) 

@[hott]
def hsquare.of_legs {C : Type _} [is_cat C] {J : Set} {f : J -> C} 
  {c d : C} (leg : Π j : J, f j ⟶ c) {j_leg : Π j : J, d ⟶ f j} {c_leg : d ⟶ c}
  (w : Π j : J, j_leg j ≫ leg j = c_leg) : hsquare leg :=
begin
  fapply cone.mk d, fapply nat_trans.mk,
  { intro s, hinduction s with j, exact j_leg j, exact c_leg },
  { intros s₁ s₂ h, hinduction s₁ with j₁, all_goals { hinduction s₂ with j₂ },
    all_goals { hinduction h },
    { change (constant_functor d).map (𝟙 _) ≫ _ = _, rwr is_precat.id_comp, 
      change _ = _ ≫ (orthogonal_tuple leg).map (𝟙 _), 
      rwr precategories.functor.map_id, rwr is_precat.comp_id },
    { rwr is_precat.id_comp, change _ = _ ≫ leg j₁, rwr w j₁ },
    { rwr is_precat.id_comp, change _ = _ ≫ (𝟙 _), rwr is_precat.comp_id } }  
end

@[hott]
def hsquare_edge {C : Type _} [is_cat C] {J : Set} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) : Π j : J, S.X ⟶ f j := 
assume j, S.π.app (inf_w_node.tip j)

@[hott]
def hsquare_diag {C : Type _} [is_cat C] {J : Set} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) : S.X ⟶ c :=
S.π.app inf_w_base 

@[hott]
def hsquare_eq {C : Type _} [is_cat C] {J : Set} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) : 
  Π (j : J), (hsquare_edge S j) ≫ leg j = hsquare_diag S :=
assume j,
calc (hsquare_edge S j) ≫ leg j = (S.π.app (inf_w_node.tip j)) ≫ 
                                     (orthogonal_tuple leg).map (inf_w_leg j) : rfl 
     ... = S.π.app (inf_w_node.base J) : by rwr cone.fac S (inf_w_leg j) 

@[hott] 
def inf_pullback_eq {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} [has_inf_pullback leg] : 
  Π j : J, inf_pullback_homo leg j ≫ leg j = inf_pullback_diag leg :=
assume j, hsquare_eq (limit.cone (orthogonal_tuple leg)) j 

@[hott]
def inf_pullback_lift {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) [has_inf_pullback leg] : 
  S.X ⟶ inf_pullback leg :=
((get_limit_cone (orthogonal_tuple leg)).is_limit.lift S).v_lift 

@[hott]
def inf_pb_lift_eq {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) [has_inf_pullback leg] : 
  Π j : J, inf_pullback_lift S ≫ inf_pullback_homo leg j = hsquare_edge S j :=
λ j,  ((get_limit_cone (orthogonal_tuple leg)).is_limit.lift S).fac (inf_w_node.tip j)  


@[hott]
def inf_pb_lift_diag_eq {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) [has_inf_pullback leg] : 
  inf_pullback_lift S ≫ inf_pullback_diag leg = hsquare_diag S :=
((get_limit_cone (orthogonal_tuple leg)).is_limit.lift S).fac inf_w_base

@[hott]
def inf_pullback_uniq {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (S : hsquare leg) [has_inf_pullback leg] : 
  Π (h : S.X ⟶ inf_pullback leg), (Π (j : J), h ≫ inf_pullback_homo leg j = 
                   hsquare_edge S j) -> h ≫ (inf_pullback_diag leg) = hsquare_diag S -> 
    h = inf_pullback_lift S :=
assume h p q,
have w : Π (iw : inf_wedge J), h ≫ (limit.cone (orthogonal_tuple leg)).π.app iw =
                                    S.π.app iw, from  
  begin intro iw, hinduction iw with j, exact p j, exact q end,
(get_limit_cone (orthogonal_tuple leg)).is_limit.uniq S (cone_map.mk h w) 


/- Monomorphisms are stable under `inf_pullback`. -/
@[hott]
def mono_is_inf_stable {C : Type u} [is_cat.{v} C] {J : Set.{u'}} {f : J -> C} 
  {c : C} {leg : Π j : J, f j ⟶ c} (H : Π j : J, is_mono (leg j)) 
  [has_inf_pullback leg] : is_mono (inf_pullback_diag leg) :=
begin
  intros d g₁ g₂ pg,
  have w₁ : Π (j : J), (g₁ ≫ inf_pullback_homo leg j) ≫ leg j = 
                                                 g₁ ≫ (inf_pullback_diag leg), from
    begin intro j, rwr is_precat.assoc, rwr inf_pullback_eq end,
  have w₂ : Π (j : J), (g₂ ≫ inf_pullback_homo leg j) ≫ leg j = 
                                                 g₂ ≫ (inf_pullback_diag leg), from
    begin intro j, rwr is_precat.assoc, rwr inf_pullback_eq end,
  have w : Π (j : J), (g₁ ≫ inf_pullback_homo leg j) = (g₂ ≫ inf_pullback_homo leg j), from
    λ j, H j d _ _ (w₁ j ⬝ pg ⬝ (w₂ j)⁻¹), 
  let S₁ := hsquare.of_legs leg w₁, let S₂ := hsquare.of_legs leg w₂,
  have p₁ : g₁ = inf_pullback_lift S₁, from inf_pullback_uniq S₁ g₁ (λ j, idp) idp,
  have p₂ : g₂ = inf_pullback_lift S₁, from 
    begin fapply inf_pullback_uniq S₁ g₂, { intro j, rwr <- w }, { rwr <- pg } end,
  exact p₁ ⬝ p₂⁻¹
end

/- The intersection of arbitrary many subobjects. -/
@[hott]
class has_subobj_iInter {C : Type u} [is_cat.{v} C] {c : C} {J : Set.{u'}} (f : J -> subobject c) :=
  (exists_inter : @has_product _ subobject_is_cat _ f)

@[hott, instance]
def has_iInter_of_has_inf_pullbacks {C : Type u} [is_cat.{v} C] 
  [has_inf_pullbacks.{v u u'} C] {c : C} {J : Set.{u'}} 
  (f : J -> subobject.{u v} c) : has_subobj_iInter f :=
begin 
  apply has_subobj_iInter.mk, apply has_product.mk, apply has_limit.mk,
  fapply limit_cone.mk, 
  { fapply fan.mk, 
    { fapply subobject.mk, exact inf_pullback (λ j : J, (f j).hom), 
      exact limit_leg (orthogonal_tuple (λ j : J, (f j).hom)) (inf_w_base), 
      exact mono_is_inf_stable (λ j, (f j).is_mono) }, 
    { intro j, fapply hom_of_monos.mk,
      { exact inf_pullback_homo _ j },
      { exact inf_pullback_eq j } } },
  { fapply is_limit.mk, 
    { intro cone_f, 
      let leg := λ j : J, (f j).hom,
      have w : Π j : J, ((cone_f.π.app j).hom_obj ≫ leg j) = cone_f.X.hom, from 
        λ j, (cone_f.π.app j).fac, 
      let S : hsquare leg := @hsquare.of_legs _ _ _ _ _ cone_f.X.obj leg 
                                        (λ j, (cone_f.π.app j).hom_obj) cone_f.X.hom w,
      fapply cone_map.mk,
      { fapply hom_of_monos.mk, exact inf_pullback_lift S, exact inf_pb_lift_diag_eq S },
      { intro j, exact is_prop.elim _ _ } }, 
    { intros cf j, exact is_prop.elim _ _ } }
end  

@[hott, instance]
def has_iInter_to_has_product {C : Type u} [is_cat.{v} C] {c : C} {J : Set} 
  (f : J -> subobject c) [H : has_subobj_iInter f] : has_product f := H.exists_inter

@[hott]
def subobject.iInter {C : Type u} [is_cat.{v} C] {c : C} {J : Set.{u'}} (f : J -> subobject c)
  [has_subobj_iInter f] : subobject c := ∏ f


end categories.inf_pullbacks

end hott