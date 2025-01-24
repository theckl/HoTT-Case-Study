import algebra.group.basic 
       

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.is_equiv subset precategories 
     categories categories.sets

namespace algebra

/- A subgroup is a subobject in the category of groups. The embedding monomorphism is
   a monomorphism of the underlying sets. So we can construct a subgroup as a subset of a 
   group inheriting the group structure. -/
@[hott]  --[GEVE]
def Subgroup (G : Group) := @subobject Group_Category G

@[hott, instance]
def subgroup_has_hom (G : Group) : has_hom (Subgroup G) :=
  by change has_hom (@subobject Group_Category G); apply_instance

@[hott, instance]
def subgroup_has_order (G : Group) : has_order (Subgroup G) :=
  by change has_order (@subobject Group_Category G); apply_instance

@[hott, instance]
def subgroup_is_set (G : Group) : is_set (Subgroup G) :=
  by change is_set (@subobject Group_Category G); apply_instance

@[hott]  --[GEVE]
def group_mon_is_inj {G H : Group} : Π (f : G ⟶ H), 
  @is_mono Group_Category _ _ f <-> 
  @set.is_set_injective (Group_to_Set_functor.obj H) (Group_to_Set_functor.obj G) 
                        (Group_to_Set_functor.map f) :=
begin 
  intro f, fapply prod.mk,
  { intro mono_f, apply mono_is_set_inj, intros A g₁ g₂ g_eq, 
    let h := to_hom_set (word_quot_Group_is_ind_free_group A).h, 
    let g₁' := ((word_quot_Group_is_ind_free_group A).map g₁).1,
    let g₂' := ((word_quot_Group_is_ind_free_group A).map g₂).1,
    have hom_eq₁ : h ≫ Group_to_Set_functor.map (g₁' ≫ f) = 
                                            h ≫ Group_to_Set_functor.map (g₂' ≫ f), from 
    begin
      rwr Group_to_Set_functor.map_comp, rwr Group_to_Set_functor.map_comp,
      apply eq_of_homotopy, intro a, 
      change Group_to_Set_functor.map f (Group_to_Set_functor.map g₁' 
                                         ((word_quot_Group_is_ind_free_group A).h _)) = 
             Group_to_Set_functor.map f (Group_to_Set_functor.map g₂' 
                                         ((word_quot_Group_is_ind_free_group A).h _)),
      rwr <- ((word_quot_Group_is_ind_free_group A).map g₁).2 a,
      rwr <- ((word_quot_Group_is_ind_free_group A).map g₂).2 a,  
      exact ap10 g_eq a
    end,
    have hom_eq₂ : g₁' = g₂', from 
    begin
      fapply mono_f, fapply (word_quot_Group_is_ind_free_group A).unique, intro a, 
      change (h ≫ Group_to_Set_functor.map (g₁' ≫ f)) a = 
                                             (h ≫ Group_to_Set_functor.map (g₂' ≫ f)) a,
      exact ap10 hom_eq₁ a
    end,
    apply eq_of_homotopy, intro a, 
    rwr ((word_quot_Group_is_ind_free_group A).map g₁).2 a,
    rwr ((word_quot_Group_is_ind_free_group A).map g₂).2 a,
    change Group_to_Set_functor.map g₁' _ = Group_to_Set_functor.map g₂' _,
    rwr hom_eq₂ },
  { intro set_inj, 
    fapply λ H, @mono_is_faithful Group_Category Set_Category Group_to_Set_functor H _ _ f, 
    apply Group_to_Set_functor_is_faithful, apply set_inj_is_mono _ set_inj }
end

@[hott]
def unit_subgroup (G : Group): Subgroup G :=
begin  
  fapply subobject.mk, exact unit_Group, exact init_group_hom G, 
  intros H f₁ f₂ f_eq, fapply Group_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro h, exact @is_prop.elim _ One_is_prop _ _
end

@[hott]
def subset_of_subgroup {G : Group} (H : Subgroup G) : 
  Subset (Group_to_Set_functor.obj G) :=
λ g, image (Group_to_Set_functor.map H.hom) g 

@[hott]
structure subgroup_str {G : Group} (H : Subset (Group_to_Set_functor.obj G)) :=
  (one : group.one G ∈ H)
  (mul : Π {g₁ g₂ : G}, g₁ ∈ H -> g₂ ∈ H -> g₁ * g₂ ∈ H)
  (inv : Π {g : G}, g ∈ H -> g⁻¹ ∈ H)

@[hott]
def subgroup_laws {G : Group} (H : Subgroup G) : subgroup_str (subset_of_subgroup H) :=
begin
  fapply subgroup_str.mk,
  { apply tr, fapply fiber.mk, exact 1, exact (group_hom_laws _).one_comp },
  { intros g₁ g₂ g₁_el g₂_el, hinduction g₁_el with fib₁, hinduction g₂_el with fib₂,
    apply tr, fapply fiber.mk, exact fib₁.1 * fib₂.1, rwr (group_hom_laws _).mul_comp,
    rwr fib₁.2, rwr fib₂.2 },
  { intros g g_el, hinduction g_el with fib, 
    apply tr, fapply fiber.mk, exact fib.1⁻¹, rwr group_hom_inv, rwr fib.2 }
end 

@[hott]
def subgroup_hom_of_subset {G : Group} (H₁ H₂ : Subgroup G) :
  (subset_of_subgroup H₁ ⊆ subset_of_subgroup H₂) -> (H₁ ⟶ H₂) :=
begin
  intro sset, 
  have fib_h : Π h, fiber (Group_to_Set_functor.map H₂.hom) 
                                                 (Group_to_Set_functor.map H₁.hom h), from 
      λ h, set.set_inj_image_to_fiber _ ((group_mon_is_inj _).1 H₂.is_mono)  
          (Group_to_Set_functor.map H₁.hom h) (sset _ (tr (fiber.mk h idp))), 
  fapply hom_of_monos.mk, 
  { fapply group_hom.mk,  
    { intro h₁, exact (fib_h h₁).1 },
    { fapply group_hom_str.mk,
      { intros h₁ h₁', apply (group_mon_is_inj _).1 H₂.is_mono, rwr (fib_h _).2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr (fib_h _).2, rwr (fib_h _).2 },
      { apply (group_mon_is_inj _).1 H₂.is_mono, rwr (fib_h _).2,
        rwr (group_hom_laws _).one_comp, rwr (group_hom_laws _).one_comp } } },
  { apply Group_to_Set_functor_is_faithful, rwr Group_to_Set_functor.map_comp,
    apply eq_of_homotopy, intro h, 
    change Group_to_Set_functor.map _ (Group_to_Set_functor.map _ h) = 
                                                           Group_to_Set_functor.map _ h, 
    exact (fib_h _).2 }
end

@[hott]
def subset_of_subgroup_hom {G : Group} {H₁ H₂ : Subgroup G} :
  (H₁ ⟶ H₂) -> (subset_of_subgroup H₁ ⊆ subset_of_subgroup H₂) :=
begin
  intros sg_hom g g_el₁, hinduction g_el₁ with fib₁, 
  rwr <- sg_hom.fac at fib₁, rwr Group_to_Set_functor.map_comp at fib₁, 
  apply tr, fapply fiber.mk,
  { exact Group_to_Set_functor.map sg_hom.hom_obj fib₁.1 },
  { exact fib₁.2 }
end 

@[hott]  --[GEVE]
def Subgroup_of_Subset {G : Group} (H : Subset (Group_to_Set_functor.obj G)) :
  subgroup_str H -> Subgroup G :=
begin  
  intro sg_str, fapply subobject.mk,
  { apply Group.mk H, fapply group.mk,
    { apply_instance },
    { intros h₁ h₂, exact ⟨@group.mul G G.struct h₁.1 h₂.1, sg_str.mul h₁.2 h₂.2⟩ },
    { intros h₁ h₂ h₃, apply pred_Set_eq, apply group.mul_assoc },
    { exact ⟨G.struct.one, sg_str.one⟩ },
    { intro h, apply pred_Set_eq, apply group.one_mul },
    { intro h, apply pred_Set_eq, apply group.mul_one },
    { intro h, exact ⟨@group.inv G G.struct h.1, sg_str.inv h.2⟩ },
    { intro h, apply pred_Set_eq, apply group.mul_left_inv } },
  { fapply group_hom.mk, 
    { exact pred_Set_map _ },
    { fapply group_hom_str.mk,
      { intros n₁ n₂, exact idp },
      { exact idp } } },
  { apply (group_mon_is_inj _).2, exact pred_Set_map_is_inj _ }
end

@[hott]  
def Subgroup_Subset_str {G : Group} (H : Subset (Group_to_Set_functor.obj G))
  (H_str : subgroup_str H) : subset_of_subgroup (Subgroup_of_Subset H H_str) = H :=  
begin
  apply eq_of_homotopy, intro g, fapply iff_eq, fapply prod.mk,
  { intro ss_g, hinduction ss_g with fib, rwr <- fib.2, exact fib.1.2 },
  { intro H_g, apply tr, change fiber (pred_Set_map H) g, fapply fiber.mk,
    { fapply dpair, exact g, exact H_g },
    { exact idp } }
end

@[hott]
def unit_subgroup_is_initial {G : Group} : Π (H : Subgroup G), unit_subgroup G ⟶ H :=
begin
  intro H, apply subgroup_hom_of_subset, intros g g_el, 
  hinduction g_el with fib, hinduction fib with h h_eq, change One at h,
  have p : h = One.star, from is_prop.elim _ _, 
  have g_one : g = 1, by rwr <- h_eq,
  rwr g_one, apply tr, apply fiber.mk, exact (group_hom_laws H.hom).one_comp
end

/- Group homomorphisms have images. -/
@[hott, instance]  --[GEVE]
def group_hom_has_image {G H : Group} (f : G ⟶ H) : 
  @has_image Group_Category _ _ f :=
begin  
  fapply has_image.mk, fapply cat_image.mk,
  { fapply Subgroup_of_Subset,
    { exact (λ h : H.carrier, image (Group_to_Set_functor.map f) h) },
    { fapply subgroup_str.mk,
      { apply tr, apply fiber.mk G.struct.one, exact (group_hom_laws f).one_comp },
      { intros h₁ h₂ h₁_el h₂_el, hinduction h₁_el with fib₁, hinduction h₂_el with fib₂,
        apply tr, apply fiber.mk (fib₁.1 * fib₂.1), 
        rwr (group_hom_laws f).mul_comp, rwr fib₁.2, rwr fib₂.2 },
      { intros h h_el, hinduction h_el with fib, 
        apply tr, fapply fiber.mk, exact has_inv.inv fib.1, 
        rwr group_hom_inv, rwr fib.2 } } },
  { fapply dpair,  
    { fapply group_hom.mk, 
      { intro m, fapply dpair, exact Group_to_Set_functor.map f m, 
        exact tr (fiber.mk m (@idp _ (Group_to_Set_functor.map f m))) },
      { fapply group_hom_str.mk,
        { intros m₁ m₂, apply pred_Set_eq, exact (group_hom_laws f).mul_comp _ _ },
        { apply pred_Set_eq, exact (group_hom_laws f).one_comp } } },
    { apply Group_to_Set_functor_is_faithful, exact idp } },
  { intros H' fac, fapply subgroup_hom_of_subset, 
    intros h el_im, change ↥(image _ _), change ↥(image _ _) at el_im,
    hinduction el_im with fib, change fiber (pred_Set_map _) h at fib,
    let p : fib.1.1 = h := fib.2,
    hinduction fib.1.2 with tr_eq m_fib, rwr <- p,
    apply tr, fapply fiber.mk, 
    { exact (Group_to_Set_functor.map fac.1) m_fib.1 }, 
    { change ((Group_to_Set_functor.map fac.fst) ≫ 
                             Group_to_Set_functor.map H'.hom) m_fib.1 = _, 
      rwr <- Group_to_Set_functor.map_comp, 
      have q : fac.1 ≫ H'.hom = f, from fac.2,
      rwr q, exact m_fib.2 } }
end

@[hott]  --[GEVE]
def gen_subgroup {G : Group} (L : Subset (Group_to_Set_functor.obj G)) :
  Subgroup G :=
@hom.image Group_Category _ _ (is_ind_free_group_of.map 
            (word_quot_Group_is_ind_free_group _) (pred_Set_map L)).1 
                               (group_hom_has_image _)

@[hott]
def gen_subgroup_subset {G : Group} (L : Subset (Group_to_Set_functor.obj G)) :
  Π (g : G), image (Group_to_Set_functor.map (is_ind_free_group_of.map 
            (word_quot_Group_is_ind_free_group _) (pred_Set_map L)).1 ) g -> 
            g ∈ subset_of_subgroup (gen_subgroup L) :=
begin 
  intros g g_im, hinduction g_im with fib,
  change ↥(g ∈ subset_of_subgroup (cat_image.mk _ _ _).subobj),
  rwr Subgroup_Subset_str, exact tr fib 
end

@[hott]
def gen_inc_gen_subgroup {G : Group} (L : Subset (Group_to_Set_functor.obj G)) :
  L ⊆ subset_of_subgroup (gen_subgroup L) :=
begin
  intros g g_el, apply gen_subgroup_subset L g, apply tr, fapply fiber.mk, 
  { apply is_ind_free_group_of.h (word_quot_Group_is_ind_free_group _),
    exact ⟨g, g_el⟩ },
  { change _ = pred_Set_map L ⟨g, g_el⟩, apply eq.inverse,
    exact (is_ind_free_group_of.map 
            (word_quot_Group_is_ind_free_group _) (pred_Set_map L)).2 ⟨g, g_el⟩ }
end

@[hott]
def gen_subgroup_min {G : Group} (L : Subset (Group_to_Set_functor.obj G)) :
  Π (H : Subgroup G), (L ⊆ (subset_of_subgroup H)) -> (gen_subgroup L ⟶ H) :=
begin
  intros H sset, fapply cat_image.univ, fapply dpair,
  { apply λ f, (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) f).1, 
    intro m, 
    exact (set.set_inj_image_to_fiber _ ((group_mon_is_inj _).1 H.is_mono) m.1 
                                                                  (sset m.1 m.2)).1 },
  { fapply is_ind_free_group_of.unique (word_quot_Group_is_ind_free_group _), intro n, 
    rwr Group_to_Set_functor.map_comp, 
    change Group_to_Set_functor.map H.hom (Group_to_Set_functor.map 
              (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) _).fst 
              (is_ind_free_group_of.h (word_quot_Group_is_ind_free_group _) n)) = _,
    rwr <- (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) _).2 n, 
    rwr <- (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) _).2 n,
    rwr (set.set_inj_image_to_fiber _ ((group_mon_is_inj _).1 H.is_mono) n.1 
                                                                  (sset n.1 n.2)).2 }
end 

@[hott]   --[GEVE]
def kernel_subgroup {G H : Group} (f : G ⟶ H) : Subgroup G :=
begin
  fapply Subgroup_of_Subset,
  { intro g, exact to_Prop (Group_to_Set_functor.map f g = 1) },
  { fapply subgroup_str.mk,
    { exact (group_hom_laws f).one_comp },
    { intros h₁ h₂ h₁_el h₂_el, 
      have p₁ : Group_to_Set_functor.map f _ = 1, from h₁_el,
      have p₂ : Group_to_Set_functor.map f _ = 1, from h₂_el,
      calc Group_to_Set_functor.map f (h₁ * h₂) = Group_to_Set_functor.map f h₁ *
                                                    Group_to_Set_functor.map f h₂ : 
               (group_hom_laws f).mul_comp h₁ h₂
         ... = 1 * 1 : by rwr p₁; rwr p₂
         ... = 1 : group.one_mul _ },
  { intros h h_el, 
    have p : Group_to_Set_functor.map f _ = 1, from h_el,
    calc Group_to_Set_functor.map f h⁻¹ = (Group_to_Set_functor.map f h)⁻¹ : 
                                                                         group_hom_inv _ _
         ... = 1⁻¹ : by rwr p
         ... = 1 : begin apply eq.inverse, fapply Group_inverse_is_unique, 
                                                               exact group.one_mul _ end } }
end

@[hott]  --[GEVE]
def trivial_kernel_is_mono {G H : Group} (f : G ⟶ H) : 
  kernel_subgroup f = unit_subgroup G <-> @is_mono Group_Category _ _ f :=
begin
  fapply prod.mk,
  { intro ker_eq, apply (group_mon_is_inj _).2, 
    intros g₁ g₂ g_eq, change ↥G at g₁, change ↥G at g₂, rwr <- group.mul_one g₁,
    rwr <- group.mul_left_inv g₂, rwr <- group.mul_assoc, 
    apply λ p, p ⬝ (group.one_mul g₂), apply ap (λ g, g * g₂),
    have g_el : ↥((g₁ * g₂⁻¹) ∈ subset_of_subgroup (unit_subgroup G)), from 
    begin 
      rwr <- ker_eq, apply tr, fapply fiber.mk,
      { fapply dpair, exact g₁ * g₂⁻¹, change Group_to_Set_functor.map f (g₁ * g₂⁻¹) = 1, 
        rwr (group_hom_laws f).mul_comp, 
        apply λ p, p ⬝ Group_left_inv_is_right_inv (Group_to_Set_functor.map f g₂), 
        rwr g_eq, rwr group_hom_inv },
      { exact idp } 
    end,
    hinduction g_el with fib, change g₁ * g₂⁻¹ = _, rwr <- fib.2 },
  { intro mono_f, fapply subobj_antisymm, 
    { apply subgroup_hom_of_subset, intros g g_el, hinduction g_el with fib,
      induction fib with h h_eq, apply tr, fapply fiber.mk, exact One.star,
      have H : set.is_set_injective (Group_to_Set_functor.map f), from 
        (group_mon_is_inj f).1 mono_f,
      change h.1 = g at h_eq, rwr <- h_eq, apply H, change Group_to_Set_functor.map f 1 = _, 
      have p : Group_to_Set_functor.map f h.fst = 1, from h.2,
      rwr p, exact (group_hom_laws _).one_comp },
    { exact unit_subgroup_is_initial (kernel_subgroup f) } }
end

@[hott]
def iInter_subgroups {G : Group.{u}} {I : Set.{v}} (f : I -> Subgroup G) :
  Subgroup G :=
begin 
  fapply Subgroup_of_Subset.{u u},
  { exact λ g, prop_resize.{u (max v u)} (to_Prop.{max v u} 
                         (∀ i : I, g ∈ subset_of_subgroup (f i))) },
  { fapply subgroup_str.mk,
    { apply prop_to_prop_resize, intro i, exact (subgroup_laws _).one },
    { intros g₁ g₂ g₁_el g₂_el, apply prop_to_prop_resize, intro i, 
      exact (subgroup_laws _).mul (prop_resize_to_prop g₁_el i) 
                                  (prop_resize_to_prop g₂_el i) },
    { intros g g_el, apply prop_to_prop_resize, intro i, 
      exact (subgroup_laws _).inv (prop_resize_to_prop g_el i) } }
end

@[hott, instance]
def subgroups_have_ind_inter {G : Group.{u}} {I : Set.{v}} : 
  @has_ind_inter (Subgroup G) I :=
has_ind_inter.mk (λ f, iInter_subgroups f)  

@[hott]
def subgroup_iInter {G : Group.{u}} {I : Set.{v}} (f : I -> Subgroup G) 
  (i : I) : (⋂ᵢ f) ≼ (f i) :=
begin 
  apply subgroup_hom_of_subset.{u u}, 
  intros g el, 
  change ↥(g ∈ subset_of_subgroup (Subgroup_of_Subset.{u u} _ _)) at el, 
  rwr Subgroup_Subset_str at el, exact prop_resize_to_prop el i,
end  

@[hott]
def subgroup_subgroup_iInter {G : Group.{u}} {I : Set.{v}} (f : I -> Subgroup G)
  (H : Subgroup G) : (Π (i : I), H ≼ f i) -> H ≼ ⋂ᵢ f :=
begin
  intro H_inc, apply subgroup_hom_of_subset.{u u}, 
  intros g el, change ↥(g ∈ subset_of_subgroup (Subgroup_of_Subset.{u u} _ _)), 
  rwr Subgroup_Subset_str, apply prop_to_prop_resize,
  intro i, exact subset_of_subgroup_hom (H_inc i) g el
end

end algebra

end hott