import algebra.group.subgroup 
       

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets

namespace algebra

--set_option pp.universes true

/- The monoid quotient of the underlying monoid of a group by a congruence relation 
   inherits the group structure and can thus be considered as a group quotient. -/
@[hott]
def group_to_monoid_rel {G : Group.{u}} (R : G -> G -> trunctype.{u} -1) :
  (Group.to_Monoid G).carrier -> (Group.to_Monoid G).carrier -> Prop :=
λ g h, R g h

@[hott, instance]
def group_to_monoid_cong {G : Group} (R : G -> G -> Prop) [H : is_congruence R] :
  is_congruence (group_to_monoid_rel R) :=
begin
  fapply λ is_equiv, @is_congruence.mk _ _ (group_to_monoid_rel R) is_equiv, 
  { exact H.to_is_equivalence },
  { exact H.mul_comp }
end

@[hott]  --[GEVE]
def quotient_Group_by_monoid_cong_rel (G : Group.{u}) 
  (R : G -> G -> trunctype.{u} -1) [C : is_congruence (group_to_monoid_rel R)] : 
  Group :=
begin
  let R' := group_to_monoid_rel R,
  fapply Group_eqv_Monoid_inv_law⁻¹ᶠ, fapply dpair,
  { exact (@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel R) C).carrier },
  { fapply group_of_mon_str.mk,
    { fapply set.set_quotient.rec, 
      { intro g, apply set.set_class_of R, change ↥(Group_to_Set_functor.obj G), exact g⁻¹ },
      { intros g g' H, apply pathover_of_eq, apply set.eq_of_setrel, change ↥(R g⁻¹ g'⁻¹),
        apply C.symm, rwr <- (group_laws _).one_mul g'⁻¹, rwr <- (group_laws _).one_mul g⁻¹,
        rwr <- (group_laws _).mul_left_inv g', rwr (group_laws _).mul_assoc, rwr (group_laws _).mul_assoc,
        fapply C.mul_comp, apply C.refl,
        rwr Group_left_inv_is_right_inv g', rwr <- Group_left_inv_is_right_inv g,
        fapply C.mul_comp, exact H, apply C.refl } },
    { fapply set.set_quotient.prec, 
      intro g, change ↥G at g, let g_inv := g⁻¹,
      apply λ p, eq.inverse ((monoid_hom_laws (@Monoid_cong_quotient (Group.to_Monoid G) 
                           (group_to_monoid_rel R) C).is_mon_quot.proj).mul_comp _ _) ⬝ p, 
      rwr (group_laws _).mul_left_inv  } }
end

@[hott]
class is_normal {G : Group} (H : Subgroup G) :=
  (conj_eq : Π (g : G), conjugated_Subgroup H g = H)

@[hott, instance]
def is_normal_is_prop {G : Group} (H : Subgroup G) : is_prop (is_normal H) :=
begin 
  fapply is_prop.mk, intros norm₁ norm₂, 
  hinduction norm₁ with conj₁, hinduction norm₂ with conj₂,
  fapply ap is_normal.mk,
  apply eq_of_homotopy, intro g, exact is_prop.elim _ _
end

@[hott]
def conj_one_id (G : Group) : conjugate G 1 = 𝟙 G :=
begin 
  apply Group_to_Set_functor_is_faithful, apply eq_of_homotopy, intro g, change ↥G at g,
  change 1 * g * 1⁻¹ = g, rwr (group_laws _).one_mul g, rwr <- group_one_inv_one, 
  change g * group.one G = g, rwr (group_laws _).mul_one g
end

@[hott]
def conj_one {G : Group} (H : Subgroup G) : conjugated_Subgroup H 1 = H :=
begin 
  fapply subobj_antisymm,
  { fapply hom_image_univ, exact 𝟙 _, rwr is_precat.id_comp, rwr conj_one_id, 
    rwr is_precat.comp_id },
  { change _ ≼ hom.image _, rwr conj_one_id, rwr is_precat.comp_id, 
    rwr subobj_is_im H, apply id_subobject }
end

@[hott]
def conj_comp {G : Group.{u}} : Π (g g' : G), conjugate G g ≫ conjugate G g' = conjugate G (g' * g) :=
begin  
  intro g, change ↥G at g, intro g', change ↥G at g',
  apply Group_to_Set_functor_is_faithful, apply eq_of_homotopy, 
  intro h, change ↥G at h, change (g' * (g * h * g⁻¹) * g'⁻¹) = (g' * g) * h * (g' * g)⁻¹,
  rwr <- (group_laws _).mul_assoc g', rwr <- (group_laws _).mul_assoc g', rwr group_mul_inv,
  rwr (group_laws _).mul_assoc _ g⁻¹ 
end

@[hott]
def conj_trans {G : Group.{u}} (H : Subgroup G) :
  Π (g g' : G), conjugated_Subgroup (conjugated_Subgroup H g) g' = conjugated_Subgroup H (g' * g) :=
begin
  intros g g', change hom.image _ = _, rwr <- group_im_comp, rwr is_precat.assoc, rwr conj_comp
end 

@[hott]
def conj_el_el {G : Group.{u}} (H : Subgroup G) : 
  Π (g h : G), h ∈ subset_of_subgroup H -> g * h * g⁻¹ ∈ subset_of_subgroup (conjugated_Subgroup H g) :=
begin
  intros g h h_el, hinduction h_el with fib, hinduction fib with h h_eq, apply tr, fapply fiber.mk,
  { fapply dpair, exact g * (Group_to_Set_functor.map H.hom h) * g⁻¹, apply tr, fapply fiber.mk h, 
    rwr Group_to_Set_functor.map_comp },
  { rwr <- h_eq } 
end

@[hott]
def conjugate_inv {G : Group} : Π (g h : G), g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h :=
begin 
  intros g h, rwr <- (group_laws _).mul_assoc g⁻¹, rwr <- (group_laws _).mul_assoc g⁻¹, 
  rwr (group_laws _).mul_assoc _ g⁻¹, rwr (group_laws _).mul_left_inv,
  rwr Group_left_inv_is_right_inv, rwr (group_laws _).one_mul, 
  change _ * group.one _ = _, rwr (group_laws _).mul_one
end 

@[hott]
def conj_inc_inc {G : Group} (H₁ H₂ : Subgroup G) :
  Π (g : G), conjugated_Subgroup H₁ g ≼ conjugated_Subgroup H₂ g -> H₁ ≼ H₂ :=
begin
  intros g conj_inc, apply subgroup_hom_of_subset, intros h h_el, change ↥G at h,
  rwr <- conjugate_inv g h, rwr <- conj_one H₂, rwr <- (group_laws _).mul_left_inv g, rwr <- conj_trans,
  apply conj_el_el, apply subset_of_subgroup_hom conj_inc, apply conj_el_el, exact h_el
end

@[hott]  --[GEVE]
def inc_conj_is_normal {G : Group} (H : Subgroup G) :
  (Π (g : G), H ≼ conjugated_Subgroup H g) -> is_normal H :=
begin
  intro inj_conj, apply is_normal.mk,
  intro g, fapply subobj_antisymm,
  { apply conj_inc_inc _ _ g⁻¹, rwr conj_trans, rwr (group_laws _).mul_left_inv, rwr conj_one H, 
    exact inj_conj g⁻¹ },
  { exact inj_conj g }
end

@[hott]
def conj_el_to_normal {G : Group} {H : Subgroup G} :
  (Π (h g : G), h ∈ subset_of_subgroup H -> g * h * g⁻¹ ∈ subset_of_subgroup H) ->
  is_normal H :=
begin
  intro conj_el, apply inc_conj_is_normal, intro g, apply subgroup_hom_of_subset, 
  intros h h_el, change ↥G at h, rwr <- conjugate_inv g⁻¹ h, rwr group_inv_inv, 
  apply conj_el_el H g,
  have el : ↥(g⁻¹ * h * (g⁻¹)⁻¹ ∈ subset_of_subgroup H), from conj_el h g⁻¹ h_el, 
  rwr group_inv_inv at el, exact el
end

@[hott, instance]  --[GEVE]
def kernel_is_normal {G H : Group} (f : G ⟶ H) : is_normal (kernel_subgroup f) :=
begin
  fapply conj_el_to_normal, intros h g h_el, hinduction h_el with fib,
  hinduction fib, hinduction point with h' h'_eq,
  change Group_to_Set_functor.map f h' = 1 at h'_eq, change h' = h at point_eq,
  rwr <- point_eq,
  apply tr, fapply fiber.mk,
  { fapply dpair, exact g * h' * g⁻¹, change Group_to_Set_functor.map f _ = 1,
    rwr (group_hom_laws _).mul_comp, rwr (group_hom_laws _).mul_comp,
    rwr h'_eq, 
    have p : Group_to_Set_functor.map f g * 1 = Group_to_Set_functor.map f g, from
                (group_laws H).mul_one _, 
    rwr p, rwr <- (group_hom_laws _).mul_comp, rwr Group_left_inv_is_right_inv,
    exact (group_hom_laws _).one_comp },
  { exact idp }
end

@[hott]
def subgroup_of_comm_group_is_normal {G : Group} (G_comm : Π (a b : G), a * b = b * a) (H : Subgroup G) :
  is_normal H :=
begin
  fapply conj_el_to_normal, intros h g h_el,
  have p : g * h * g⁻¹ = h, from 
    calc g * h * g⁻¹ = h * g * g⁻¹ : by rwr G_comm g h
         ... = h * (g * g⁻¹) : (group_laws G).mul_assoc _ _ _
         ... = h * 1 : by rwr Group_left_inv_is_right_inv
         ... = h : (group_laws G).mul_one h, 
  rwr p, exact h_el
end

@[hott, instance]
def unit_subgroup_is_normal (G : Group) : is_normal (unit_subgroup G) :=
begin  
  fapply conj_el_to_normal, intros h g h_el, hinduction h_el with fib,
  hinduction fib with h' h'_eq, change One at h',
  have p : h' = One.star, from is_prop.elim _ _, 
  rwr p at h'_eq, 
  have q : h = 1, by rwr <- h'_eq, rwr q, apply tr, fapply fiber.mk,
  { exact 1 },
  { change _ = _ * group.one G * _, rwr (group_laws _).mul_one, rwr Group_left_inv_is_right_inv }
end

/- The extra structure on groups compared to monoids associates equivalence relations 
   and congruences to subgroups and normal subgroups. -/

@[hott]
def subgroup_to_rel {G : Group.{u}} (H : Subgroup G) : G -> G -> Prop := 
  λ g h : G, to_Prop (g⁻¹ * h ∈ subset_of_subgroup H)

@[hott, instance]  --[GEVE]
def subgroup_rel_is_equiv {G : Group} (H : Subgroup G) : 
  is_equivalence (λ g h, subgroup_to_rel H g h) :=
begin 
  fapply is_equivalence.mk,
  { intro g, change ↥(g⁻¹ * g ∈ subset_of_subgroup H), 
    rwr (group_laws _).mul_left_inv, exact (subgroup_laws _).one },
  { intros g h rel, change ↥(h⁻¹ * g ∈ subset_of_subgroup H), 
    rwr <- group_inv_inv g, rwr <- group_mul_inv, apply (subgroup_laws _).inv,
    exact rel },
  { intros g₁ g₂ g₃ rel₁ rel₂, change ↥(g₁⁻¹ * g₃ ∈ subset_of_subgroup H), 
    rwr <- (group_laws _).mul_one g₁⁻¹, change ↥(g₁⁻¹ * 1 * g₃∈subset_of_subgroup H), 
    rwr <- Group_left_inv_is_right_inv g₂, 
    rwr <- (group_laws _).mul_assoc g₁⁻¹, rwr (group_laws _).mul_assoc _ _ g₃, 
    apply (subgroup_laws _).mul, exact rel₁, exact rel₂ }  
end

@[hott]  --[GEVE]
def subgroup_rel_cong_to_normal {G : Group} (H : Subgroup G) :
  is_congruence (λ g h : G, subgroup_to_rel H g h) -> is_normal H :=
begin 
  intro is_cong, apply inc_conj_is_normal, intro g, apply conj_inc_inc _ _ g⁻¹, rwr conj_trans,
  rwr (group_laws _).mul_left_inv, rwr conj_one, 
  { apply subgroup_hom_of_subset, intros h' h'_el, hinduction h'_el with fib,
    hinduction fib.1.2 with h_tr h_el_conj, hinduction h_el_conj with h el_conj,
    let h'_eq := fib.2, let p := el_conj ⬝ h'_eq, rwr <- p, 
    let h'' := Group_to_Set_functor.map H.hom h, change ↥(g⁻¹ * h'' * (g⁻¹)⁻¹ ∈ _), rwr group_inv_inv,
    rwr <- (group_laws _).one_mul (g⁻¹ * (Group_to_Set_functor.map H.hom h) * g), rwr group_one_inv_one,
    change ↥(subgroup_to_rel H 1 (g⁻¹ * h'' * g)), 
    rwr <- (group_laws _).mul_left_inv g, fapply is_cong.mul_comp, 
    { rwr <- (group_laws _).mul_one g⁻¹, fapply is_cong.mul_comp,
      { rwr (group_laws _).mul_one, apply (subgroup_rel_is_equiv _).refl },
      { change ↥((1:G)⁻¹ * h'' ∈ _), rwr <- group_one_inv_one G, rwr (group_laws _).one_mul,
        apply tr, apply fiber.mk h, exact idp } }, 
    { apply (subgroup_rel_is_equiv _).refl } },
end

@[hott, instance]  --[GEVE]
def normal_subgroup_to_cong_rel {G : Group} (H : Subgroup G) [norm_H : is_normal H] : 
  is_congruence (λ g h : G, subgroup_to_rel H g h) :=
begin
  fapply λ is_equiv, @is_congruence.mk _ _
            (λ g h : Monoid_to_Set_functor.obj (Group.to_Monoid G), subgroup_to_rel H g h)
            is_equiv,
  { change is_equivalence (λ g h : G, subgroup_to_rel H g h), apply_instance },
  { intros g₁ g₁' g₂ g₂' rel₁ rel₂, 
    change ↥G at g₁, change ↥G at g₁', change ↥G at g₂, change ↥G at g₂',
    change ↥((g₁ * g₂)⁻¹ * (g₁' * g₂') ∈ subset_of_subgroup H),
    rwr group_mul_inv, rwr (group_laws _).mul_assoc, 
    rwr <- (group_laws _).mul_assoc g₁⁻¹, rwr <- (group_laws _).mul_assoc g₂⁻¹,
    rwr <- (group_laws _).one_mul g₂', rwr <- (group_laws _).mul_left_inv g₂⁻¹,
    rwr group_inv_inv, rwr (group_laws _).mul_assoc g₂, 
    rwr <- (group_laws _).mul_assoc _ g₂ _, fapply (subgroup_laws _).mul,
    { let g₂_inv := g₂⁻¹, change ↥(g₂_inv * _ * _ ∈ _), rwr <- group_inv_inv g₂,
      change ↥(g₂⁻¹ * _ * _ ∈ _), rwr <- norm_H.conj_eq, fapply conj_el_el, exact rel₁ },
    { exact rel₂ } }
end

@[hott]  --[GEVE]
def cong_rel_to_normal_subgroup {G : Group} (R : G -> G -> Prop) :
  is_congruence (λ g h, R g h) -> Σ (H : Subgroup G), is_normal H :=
begin
  intro cong, 
  have equiv : is_equivalence (λ g h, R g h), from cong.to_is_equivalence,
  fapply dpair,
  { fapply Subgroup_of_Subset, 
    { intro g, exact R g 1 },
    { fapply subgroup_str.mk,
      { exact @is_equivalence.refl _ (λ g h, R g h) equiv 1 },
      { intros g₁ g₂ g₁_el g₂_el,  
        rwr <- (group_laws _).mul_one 1, apply cong.mul_comp, exact g₁_el, exact g₂_el },
      { intros g g_el, rwr <- (group_laws _).mul_left_inv g, 
        rwr <- (group_laws _).mul_one g⁻¹, rwr (group_laws _).mul_assoc g⁻¹,
        apply cong.mul_comp, 
        { exact @is_equivalence.refl _ (λ g h, R g h) equiv g⁻¹ },
        { change ↥(R 1 (1 * g)), rwr (group_laws _).one_mul,
          apply @is_equivalence.symm _ (λ g h, R g h) equiv, exact g_el } } } },
  { apply conj_el_to_normal, intros h g h_el, apply tr, fapply fiber.mk,
    { fapply dpair, exact g * h * g⁻¹, change ↥(R (g * h * g⁻¹) 1), 
      rwr <- Group_left_inv_is_right_inv g, fapply cong.mul_comp,
      { rwr <- (group_laws _).mul_one g, rwr (group_laws _).mul_assoc g, 
        change ↥(R (g * (1 * h)) _), rwr (group_laws _).one_mul h, fapply cong.mul_comp,
        { exact @is_equivalence.refl _ (λ g h, R g h) equiv g },
        { hinduction h_el with fib, 
          have p : fib.1.1 = h, from fib.2, rwr <- p, exact fib.1.2 } },
      { exact @is_equivalence.refl _ (λ g h, R g h) equiv g⁻¹ } },
    { exact idp } } 
end 

@[hott]
def cong_rel_to_subgroup_rinv {G : Group} (R : G -> G -> Prop)
  (is_cong : is_congruence (λ g h, R g h)) : 
  subgroup_to_rel (cong_rel_to_normal_subgroup R is_cong).1 = (λ a b, R a b) :=
begin
  apply eq_of_homotopy2, intros g h, fapply iff_eq, 
  change ↥(g⁻¹ * h ∈ subset_of_subgroup 
                            (cong_rel_to_normal_subgroup R is_cong).fst) <-> _, 
  change ↥(g⁻¹ * h ∈ subset_of_subgroup (Subgroup_of_Subset _ _)) <-> _, 
  rwr Subgroup_Subset_str, fapply prod.mk,
  { intro norm_rel, apply is_equivalence.symm (λ g h, R g h), 
    rwr <- (group_laws _).one_mul h, rwr <- (group_laws _).mul_one g,
    rwr <- Group_left_inv_is_right_inv g, rwr (group_laws _).mul_assoc,    
    apply is_cong.mul_comp, apply is_equivalence.refl (λ g h, R g h), exact norm_rel },
  { intro rel, apply is_equivalence.symm (λ g h, R g h),
    rwr <- (group_laws _).mul_left_inv g, apply is_cong.mul_comp,
    apply is_equivalence.refl (λ g h, R g h), exact rel }
end

@[hott]  --[GEVE]
structure is_group_quotient {G : Group} (H : Subgroup G) [is_normal H] 
  (Q : Group) :=
(proj : G ⟶ Q)
(surj : is_surjective (Group_to_Set_functor.map proj))
(ker : kernel_subgroup proj = H)

@[hott]
def quotient_Group_by_normal_subgroup (G : Group) (H : Subgroup G) [norm_H : is_normal H] :
  Group :=
quotient_Group_by_monoid_cong_rel G (subgroup_to_rel H)

@[hott]  --[GEVE]
def quot_Group_is_group_quot {G : Group.{u}} (H : Subgroup G) [norm_H : is_normal H] :
  is_group_quotient H (quotient_Group_by_normal_subgroup G H) :=
begin
  have equiv : is_equivalence (λ g h, subgroup_to_rel H g h), from 
    (normal_subgroup_to_cong_rel H).to_is_equivalence, 
  fapply is_group_quotient.mk, 
  { apply group_of_monoid_hom, 
    exact (@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                                        (subgroup_to_rel H)) _).is_mon_quot.proj },
  { rwr Group_to_Monoid_to_Set_functor, 
    rwr (@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                                        (subgroup_to_rel H)) _).is_mon_quot.proj_eq, 
    intro q, hinduction (@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                   (subgroup_to_rel H)) _).is_mon_quot.is_set_quot.gen q with fib_eq fib, 
    apply tr, exact fiber.mk fib.1 fib.2 }, 
  { fapply subobj_antisymm, 
    { apply subgroup_hom_of_subset, intros h h_el, hinduction h_el with fib,
      hinduction fib, hinduction point with h' h_eq, 
      change h' = h at point_eq, rwr <- point_eq,
      rwr <- (group_laws _).one_mul h', rwr group_one_inv_one, 
      change ↥(subgroup_to_rel H 1 h'), 
      apply @is_equivalence.symm _ (λ g h, subgroup_to_rel H g h) equiv,
      change ↥(group_to_monoid_rel (subgroup_to_rel H) _ _),
      apply ((@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                            (subgroup_to_rel H)) _).is_mon_quot.is_set_quot.eq _ _).1,
      rwr <- (@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                                    (subgroup_to_rel H)) _).is_mon_quot.proj_eq,
      change Group_to_Set_functor.map _ _ = _ at h_eq,
      rwr Group_to_Monoid_to_Set_functor at h_eq, rwr h_eq },
    { apply subgroup_hom_of_subset, intros h h_el, apply tr, fapply fiber.mk,
      { fapply dpair, exact h, change Group_to_Set_functor.map _ _ = _, 
        rwr Group_to_Monoid_to_Set_functor, 
        rwr <- (group_laws _).one_mul h at h_el, rwr group_one_inv_one at h_el, 
        change ↥(subgroup_to_rel H 1 h) at h_el, 
        change ↥(group_to_monoid_rel (subgroup_to_rel H) _ _) at h_el,
        rwr (@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                                    (subgroup_to_rel H)) _).is_mon_quot.proj_eq,
        rwr <- ((@Monoid_cong_quotient (Group.to_Monoid G) (group_to_monoid_rel 
                      (subgroup_to_rel H)) _).is_mon_quot.is_set_quot.eq _ _).2 h_el }, 
      { exact idp } } }
end

@[hott]  --[GEVE]
def group_quot_is_monoid_quot {G : Group} (H : Subgroup G) [norm_H : is_normal H]
  (Q : Group) : is_group_quotient H Q -> @is_monoid_quotient (Group.to_Monoid G) 
     (group_to_monoid_rel (subgroup_to_rel H)) _ (Group.to_Monoid Q):=
begin
  intro is_quot, fapply is_monoid_quotient.mk,
  { exact (concrete_forget_functor (Group.to_Monoid)).map is_quot.proj },
  { fapply set.is_cons_quotient.mk, 
    { exact Monoid_to_Set_functor.map 
                      ((concrete_forget_functor Group.to_Monoid).map is_quot.proj) },
    { intro q, hinduction is_quot.surj q with tr_eq fib, apply tr,
      apply dpair fib.1, exact fib.2 },
    { intros g₁ g₂, fapply prod.mk,
      { intro g_eq, change ↥G at g₁, change ↥G at g₂, 
        change ↥(g₁⁻¹ * g₂ ∈ subset_of_subgroup H), rwr <- is_quot.ker,
        apply tr, fapply fiber.mk,
        { fapply dpair (g₁⁻¹ * g₂),
          change Group_to_Set_functor.map is_quot.proj (g₁⁻¹ * g₂) = 1,
          rwr (group_hom_laws _).mul_comp, rwr group_hom_inv,
          apply λ p, p ⬝ (group_laws _).mul_left_inv 
                                        (Group_to_Set_functor.map is_quot.proj g₁), 
          
          exact ap (λ g, (Group_to_Set_functor.map is_quot.proj g₁)⁻¹ * g) g_eq⁻¹ },
        { exact idp } },
      { intro rel, change ↥G at g₁, change ↥G at g₂,
        change ↥(g₁⁻¹ * g₂ ∈ subset_of_subgroup H) at rel, 
        hinduction rel with fib, rwr <- is_quot.ker at fib, 
        hinduction fib with h h_eq, hinduction h with h ker_eq,
        change Group_to_Set_functor.map is_quot.proj h = 1 at ker_eq,
        change h = g₁⁻¹ * g₂ at h_eq, rwr h_eq at ker_eq, 
        change Group_to_Set_functor.map is_quot.proj g₁ = 
                                          Group_to_Set_functor.map is_quot.proj g₂,
        apply group_left_cancel (Group_to_Set_functor.map is_quot.proj g₁⁻¹), 
        rwr <- (group_hom_laws _).mul_comp, rwr <- (group_hom_laws _).mul_comp, 
        rwr (group_laws _).mul_left_inv, rwr ker_eq, 
        exact (group_hom_laws is_quot.proj).one_comp } } },
  { exact idp }
end

@[hott]
def group_image_is_quot {G H : Group} (f : G ⟶ H) : 
  @is_group_quotient G (@kernel_subgroup G H f) (kernel_is_normal f) (hom.image f).obj :=
begin
  fapply is_group_quotient.mk,
  { exact hom_to_image f },
  { apply hom_to_image_is_surj },
  { fapply subobj_antisymm,
    { apply subgroup_hom_of_subset, intros h h_el, hinduction h_el with fib,
      hinduction fib, hinduction point with h' h_eq, 
      change h' = h at point_eq, rwr <- point_eq, 
      change Group_to_Set_functor.map _ _ = _ at h_eq,
      apply tr, fapply fiber.mk,
      { fapply dpair, exact h', change Group_to_Set_functor.map _ _ = _,
        rwr <- hom_to_image_eq f,
        rwr Group_to_Set_functor.map_comp,
        change Group_to_Set_functor.map (hom.image f).hom (Group_to_Set_functor.map (hom_to_image f) h') = 1,
        rwr h_eq },
      { exact idp } },
    { apply subgroup_hom_of_subset, intros h h_el, hinduction h_el with fib,
      hinduction fib, hinduction point with h' h_eq, 
      change h' = h at point_eq, rwr <- point_eq,
      change Group_to_Set_functor.map _ _ = _ at h_eq,
      apply tr, fapply fiber.mk,
      { fapply dpair, exact h', change Group_to_Set_functor.map _ _ = _,
        rwr <- hom_to_image_eq f at h_eq,
        rwr Group_to_Set_functor.map_comp at h_eq,
        change Group_to_Set_functor.map (hom.image f).hom
                                         (Group_to_Set_functor.map (hom_to_image f) h') = 1 at h_eq,
        have inj : set.is_set_injective (Group_to_Set_functor.map (hom.image f).hom), from
          begin apply (group_mon_is_inj _).1, exact subobject.is_mono _ end,
        apply inj, 
        have p : Group_to_Set_functor.map (hom.image f).hom 1 = 1, from
          (group_hom_laws _).one_comp, 
        rwr p, exact h_eq },
      { exact idp } } }
end 

@[hott]
def quotient_by_unit_subgroup (G : Group) : @is_group_quotient _ (unit_subgroup G) (unit_subgroup_is_normal G) G :=
begin  
  fapply is_group_quotient.mk,
  { exact 𝟙 G },
  { intro g, apply tr, apply fiber.mk g, exact idp },
  { fapply (trivial_kernel_is_mono _).2,  
    change is_mono (id_iso G).hom, exact isos_are_mono (id_iso _) }
end

/- We define the universal property of a quotient by a normal subgroup and show the
   equivalence with the direct definition. -/
@[hott]
structure is_univ_group_quotient {G : Group} (H : Subgroup G) [is_normal H] 
  (Q : Group) :=
(proj : G ⟶ Q)
(ker : kernel_subgroup proj = H)
(factors : Π {P : Group} (f : G ⟶ P), H ≼ kernel_subgroup f -> 
                                                 Σ (g : Q ⟶ P), f = proj ≫ g)
(unique : Π (P : Group) (g₁ g₂ : Q ⟶ P), proj ≫ g₁ = proj ≫ g₂ -> g₁ = g₂)

@[hott]
def group_mon_quot_fac {G : Group} {H : Subgroup G} [is_normal H] 
  {Q : Group} (is_quot : is_group_quotient H Q) {P : Group} (f : G ⟶ P) 
  (H_ker : H ≼ kernel_subgroup f) : Σ (g : Group.to_Monoid Q ⟶ Group.to_Monoid P),
      (concrete_forget_functor (Group.to_Monoid)).map f = 
                          (concrete_forget_functor Group.to_Monoid).map is_quot.proj ≫ g :=
begin
  have p : (concrete_forget_functor Group.to_Monoid).map is_quot.proj =
           (monoid_to_univ_quotient 
                        _ _ (group_quot_is_monoid_quot H Q is_quot)).proj, from idp,
  rwr p, fapply λ is_mon_quot, @is_univ_monoid_quotient.factors _ _ _ 
                               (Group.to_Monoid Q) is_mon_quot (Group.to_Monoid P),
  intros g₁ g₂ rel, change ↥G at g₁, change ↥G at g₂, 
  change Group_to_Set_functor.map f g₁ = Group_to_Set_functor.map f g₂,
  apply group_left_cancel (Group_to_Set_functor.map f g₁⁻¹), 
  rwr <- (group_hom_laws _).mul_comp, rwr <- (group_hom_laws _).mul_comp, 
  rwr (group_laws _).mul_left_inv, 
  hinduction subset_of_subgroup_hom H_ker _ rel with tr_eq fib,
  hinduction fib with h h_eq, hinduction h with h ker_eq,
  change Group_to_Set_functor.map f h = 1 at ker_eq,
  change h = g₁⁻¹ * g₂ at h_eq, rwr h_eq at ker_eq, rwr ker_eq, 
  exact (group_hom_laws f).one_comp
end 

@[hott]
def group_quotient_factors {G : Group} {H : Subgroup G} [is_normal H] 
  {Q : Group} (is_quot : is_group_quotient H Q) : Π {P : Group} (f : G ⟶ P), 
  H ≼ kernel_subgroup f → (Σ (g : ↥(Q ⟶ P)), f = is_quot.proj ≫ g) :=
begin 
  intros P f H_ker, fapply dpair,
  { apply group_of_monoid_hom, exact (group_mon_quot_fac is_quot f H_ker).1 },
  { apply concrete_forget_functor_is_faithful Group.to_Monoid,
    rwr (concrete_forget_functor (Group.to_Monoid)).map_comp, 
    change _ = _ ≫ (group_mon_quot_fac is_quot f H_ker).fst,
    let p := (group_mon_quot_fac is_quot f H_ker).2, apply λ q, p ⬝ q, 
    apply ap (λ f, (concrete_forget_functor Group.to_Monoid).map is_quot.proj ≫ f),
    exact idp }
end

@[hott]
def group_quotient_is_univ {G : Group} (H : Subgroup G) [is_normal H] 
  (Q : Group) : is_group_quotient H Q -> is_univ_group_quotient H Q :=
begin
  intro is_quot, fapply is_univ_group_quotient.mk,
  { exact is_quot.proj },
  { exact is_quot.ker },
  { intros P f H_ker, exact group_quotient_factors is_quot f H_ker },
  { intros P f₁ f₂ comp_eq, apply concrete_forget_functor_is_faithful Group.to_Monoid,
    have mon_quot_unique : Π (g₁ g₂ : Group.to_Monoid Q ⟶ Group.to_Monoid P), 
      (monoid_to_univ_quotient 
                        _ _ (group_quot_is_monoid_quot H Q is_quot)).proj ≫ g₁ = 
      (monoid_to_univ_quotient 
                        _ _ (group_quot_is_monoid_quot H Q is_quot)).proj ≫ g₂ -> 
      g₁ = g₂, by fapply λ is_mon_quot, @is_univ_monoid_quotient.unique _ _ _ 
                               (Group.to_Monoid Q) is_mon_quot (Group.to_Monoid P),
    apply mon_quot_unique, 
    change (concrete_forget_functor Group.to_Monoid).map _ ≫ _ =
           (concrete_forget_functor Group.to_Monoid).map _ ≫ _,
    rwr <- (concrete_forget_functor (Group.to_Monoid)).map_comp, 
    exact ap (@precategories.functor.map _ _ _ _ 
                        (concrete_forget_functor (Group.to_Monoid)) _ _) comp_eq } 
end

@[hott]
def univ_iso_group_quotient {G : Group} (H : Subgroup G) [is_normal H] 
  (Q : Group) (is_quot : is_univ_group_quotient H Q) : 
  Q ≅ quotient_Group_by_normal_subgroup G H :=
begin
  let is_quot' : is_univ_group_quotient H (quotient_Group_by_monoid_cong_rel G 
                                                       (subgroup_to_rel H)) := 
      group_quotient_is_univ _ _ (quot_Group_is_group_quot _),
  have H_inc : H ≼ kernel_subgroup is_quot.proj, by rwr is_quot.ker; exact 𝟙 H,
  have H_inc' : H ≼ kernel_subgroup (quot_Group_is_group_quot _).proj, by 
                                   rwr (quot_Group_is_group_quot _).ker; exact 𝟙 H,
  have p : is_quot.proj = is_quot'.proj ≫ (is_quot'.factors is_quot.proj H_inc).fst, from 
        (is_univ_group_quotient.factors is_quot' is_quot.proj H_inc).2,
  have p' : (quot_Group_is_group_quot _).proj = is_quot.proj ≫ (is_quot.factors 
                  (quot_Group_is_group_quot _).proj H_inc').fst, from 
          (is_univ_group_quotient.factors is_quot (quot_Group_is_group_quot _).proj 
                                                                          H_inc').2,
   fapply iso.mk,
    { fapply sigma.fst (is_univ_group_quotient.factors is_quot 
                                        (quot_Group_is_group_quot _).proj H_inc') },
    { fapply is_iso.mk,
      { fapply sigma.fst (is_univ_group_quotient.factors is_quot' is_quot.proj H_inc) },
      { fapply is_univ_group_quotient.unique is_quot', 
        rwr <- is_precat.assoc, rwr <- p, rwr <- p' },
      { fapply is_univ_group_quotient.unique is_quot, 
        rwr <- is_precat.assoc, rwr <- p', 
        change is_quot'.proj ≫ _ = _, rwr <- p, rwr is_precat.comp_id } } 
end 

@[hott]
def univ_iso_group_quotient_proj_eq {G : Group} (H : Subgroup G) [is_normal H] 
  (Q : Group) (is_quot : is_univ_group_quotient H Q) :
  is_quot.proj = (quot_Group_is_group_quot _).proj ≫ 
                                  (univ_iso_group_quotient H Q is_quot).ih.inv := 
begin
  apply λ (H_inc : H ≼ kernel_subgroup is_quot.proj), (is_univ_group_quotient.factors 
                 (group_quotient_is_univ _ _ (quot_Group_is_group_quot _)) is_quot.proj H_inc).2,
end 

@[hott]
def univ_is_group_quotient {G : Group} (H : Subgroup G) [is_normal H] 
  (Q : Group) : is_univ_group_quotient H Q -> is_group_quotient H Q :=
begin
  intro is_quot, fapply is_group_quotient.mk,
  { exact is_quot.proj },
  { intro g, rwr univ_iso_group_quotient_proj_eq H Q is_quot,
    hinduction is_group_quotient.surj (quot_Group_is_group_quot _) 
      (Group_to_Set_functor.map (univ_iso_group_quotient H Q is_quot).hom g) with 
      tr_eq fib, 
    rwr Group_to_Set_functor.map_comp, apply tr, fapply fiber.mk,
    { exact fib.1 },
    { change Group_to_Set_functor.map _ _ = _, rwr fib.2,
      change (Group_to_Set_functor.map (univ_iso_group_quotient H Q is_quot).hom ≫ 
        Group_to_Set_functor.map (univ_iso_group_quotient H Q is_quot).ih.inv) _ = _, 
      rwr <- Group_to_Set_functor.map_comp, 
      rwr (univ_iso_group_quotient H Q is_quot).ih.l_inv } },
  { exact is_quot.ker }
end 
/- Note that the projections of the universal and the direct group structure of `Q`
   are not automtically (= judgmentally) equal if we just transfer 
   `is_group_quotient` along the equality induced by the isomorphism of the quotient
   groups. -/

/- We characterize the normal closure of an arbitrary subgroup, construct it by 
   generators and show the connection to the closure of an equivalence relation to 
   a congruence. -/
@[hott]
structure is_normal_closure {G : Group} (H N_H : Subgroup G) :=
  (norm : is_normal N_H)
  (inc : H ≼ N_H)
  (small : Π (N : Subgroup G) [is_normal N], H ≼ N -> N_H ≼ N)

@[hott]
def normal_cong_closure {G : Group} (H N_H : Subgroup G) 
  (norm_clos : is_normal_closure H N_H) : 
  Π (g h : G), subgroup_to_rel N_H g h <-> @rel_to_cong_rel (Group.to_Monoid G) 
                                (group_to_monoid_rel (subgroup_to_rel H)) g h :=
begin
  intros g h, fapply prod.mk,
  { intro norm_rel, 
    change ↥((λ g h : G, @rel_to_cong_rel (Group.to_Monoid G) 
                            (group_to_monoid_rel (subgroup_to_rel H)) g h) g h),
    rwr <- cong_rel_to_subgroup_rinv (@rel_to_cong_rel (Group.to_Monoid G) 
              (group_to_monoid_rel (subgroup_to_rel H))) 
             (@cong_clos_rel_is_cong_rel (Group.to_Monoid G)(group_to_monoid_rel 
                                                            (subgroup_to_rel H))),
    change ↥(g⁻¹ * h ∈ _) at norm_rel, change ↥(g⁻¹ * h ∈ _), 
    apply @subset_of_subgroup_hom G N_H _, 
    { change N_H ≼ _, 
      fapply λ is_norm, is_normal_closure.small norm_clos 
                           (cong_rel_to_normal_subgroup _ _).1 is_norm, 
      { apply subgroup_hom_of_subset, intros g g_el, 
        change ↥(g ∈ subset_of_subgroup (Subgroup_of_Subset _ _)),
        rwr Subgroup_Subset_str, 
        change ↥(@rel_to_cong_rel (Group.to_Monoid G) (group_to_monoid_rel 
                                                            (subgroup_to_rel H)) g 1),
        apply cong_rel_ext_rel, change ↥(g⁻¹ * 1∈subset_of_subgroup H),
        have p : g⁻¹ * 1 = g⁻¹, from (group_laws _).mul_one g⁻¹,
        rwr p, exact (subgroup_laws _).inv g_el },
      { exact (cong_rel_to_normal_subgroup _ _).2 } }, 
    { exact norm_rel } },
  { fapply λ cong_N_H ext, @cong_clos_rel_is_min_cong (Group.to_Monoid G) 
               (group_to_monoid_rel (subgroup_to_rel H)) _ cong_N_H ext, 
    { exact @normal_subgroup_to_cong_rel _ _ norm_clos.norm },
    { intros g h, change ↥(g⁻¹ * h ∈ _) -> ↥(g⁻¹ * h ∈ _), 
      apply subset_of_subgroup_hom, exact norm_clos.inc } }
end

@[hott]
def normal_inter_closure {G : Group} (H : Subgroup G) : Subgroup G :=
begin
  let I : Set := set.to_Set (Σ (H' : Subgroup G), (H ≼ H') × (is_normal H')),
  apply @iInter_subgroups G I (λi : I, i.1)
end

@[hott]
def normal_conj_el {G : Group} (H : Subgroup G) :
  is_normal H -> Π (g h : G), h ∈ subset_of_subgroup H -> g * h * g⁻¹ ∈ subset_of_subgroup H :=
begin intros norm_H g h h_el, rwr <- @is_normal.conj_eq _ H norm_H g, apply conj_el_el, exact h_el end 

@[hott]
def normal_inter_closure_is_normal_closure {G : Group} (H : Subgroup G) :
  is_normal_closure H (normal_inter_closure H) :=
begin
  fapply is_normal_closure.mk,
  { apply conj_el_to_normal, intros h g h_el,
    change ↥(g * h * g⁻¹ ∈ subset_of_subgroup (Subgroup_of_Subset _ _)), 
    rwr Subgroup_Subset_str, apply prop_to_prop_resize,
    intro i, fapply normal_conj_el, exact i.2.2, 
    apply subset_of_subgroup_hom (subgroup_iInter _ i) h, 
    change ↥(h ∈ subset_of_subgroup (Subgroup_of_Subset _ _)) at h_el, 
    rwr Subgroup_Subset_str at h_el,
    change ↥(h ∈ subset_of_subgroup (Subgroup_of_Subset _ _)), 
    rwr Subgroup_Subset_str, exact h_el },
  { apply subgroup_subgroup_iInter, intro i, exact i.2.1 },
  { let I : Set := set.to_Set (Σ (H' : Subgroup G), (H ≼ H') × (is_normal H')),
    intros N norm_N inc_N, let i := dpair N (prod.mk inc_N norm_N),
    change @iInter_subgroups G I (λ i : I, i.1) ≼ i.1, 
    apply subgroup_iInter }
end

@[hott]
def normal_gen_closure {G : Group} (H : Subgroup G) : Subgroup G :=
  gen_subgroup (λ gh : set.to_Set (↥G × ↥(H.obj)), 
                                             gh.1 * (Group_to_Set_functor.map H.hom gh.2) * gh.1⁻¹)

@[hott]
def normal_gen_closure_is_normal_closure {G : Group} (H : Subgroup G) :
  is_normal_closure H (normal_gen_closure H) :=
begin
  change is_normal_closure H (gen_subgroup _), fapply is_normal_closure.mk,
  { apply inc_conj_is_normal, intro g, apply gen_subgroup_min,
    intro l, hinduction l with g' h, 
    have p : g' * Group_to_Set_functor.map H.hom h * g'⁻¹ = 
                  g * ((g⁻¹ * g') * Group_to_Set_functor.map H.hom h * (g⁻¹ * g')⁻¹) * g⁻¹, from 
    begin
      rwr group_mul_inv, rwr <- (group_laws _).mul_assoc g, rwr (group_laws _).mul_assoc g⁻¹,
      rwr <- (group_laws _).mul_assoc g, rwr Group_left_inv_is_right_inv, rwr (group_laws _).one_mul,
      rwr (group_laws _).mul_assoc _ _ g⁻¹, rwr (group_laws _).mul_assoc _ _ g⁻¹, 
      rwr (group_laws _).mul_left_inv, change _ = _ * (_ * group.one G), rwr (group_laws _).mul_one
    end,
    rwr p, apply conj_el_el, apply group_gen_el (λ gh : set.to_Set (↥G × ↥(H.obj)), 
                                       gh.1 * (Group_to_Set_functor.map H.hom gh.2) * gh.1⁻¹) ⟨(g⁻¹ * g'), h⟩ },
  { apply subgroup_hom_of_subset, intros h h_el, hinduction h_el with fib, hinduction fib with h' h_el,
    have p : h = (λ gh : set.to_Set (↥G × ↥(H.obj)), 
                gh.1 * (Group_to_Set_functor.map H.hom gh.2) * gh.1⁻¹)⟨(1:G),h'⟩, from 
    begin
      change h = (1 : G) * (Group_to_Set_functor.map H.hom h') * (1 : G)⁻¹, rwr (group_laws _).one_mul, 
      rwr <- group_one_inv_one, rwr h_el, apply eq.inverse, exact (group_laws _).mul_one _
    end,
    rwr p, apply group_gen_el },
  { intros N norm_N H_inc_N, apply gen_subgroup_min,
    intro l, apply normal_conj_el _ norm_N, apply subset_of_subgroup_hom H_inc_N, 
    apply tr, fapply fiber.mk, exact l.2, exact idp }
end

end algebra

end hott