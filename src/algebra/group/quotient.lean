import algebra.group.basic 
       

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets

namespace algebra

@[hott]  --[GEVE]
def quotient_Group_by_monoid_cong_rel (G : Group) 
  (R : Monoid_to_Set_functor.obj (Group.to_Monoid G) -> 
       Monoid_to_Set_functor.obj (Group.to_Monoid G) -> Prop)
  [C : is_congruence R] : Group :=
begin
  fapply Group_eqv_Monoid_inv_law⁻¹ᶠ, fapply dpair,
  { exact (Monoid_cong_quotient R).carrier },
  { fapply dpair,
    { fapply set.set_quotient.rec, 
      { intro g, apply set.set_class_of R, change ↥(Group_to_Set_functor.obj G), exact g⁻¹ },
      { intros g g' H, apply pathover_of_eq, apply set.eq_of_setrel,
        change ↥G at g, change ↥G at g', let g_inv := g⁻¹, let g'_inv := g'⁻¹, 
        have rel : ↥(R (g_inv * g) (g'_inv * g)), from 
        begin 
          rwr (group_laws _).mul_left_inv g, rwr <- (group_laws _).mul_left_inv g', 
          fapply C.mul_comp, apply (is_congruence.to_is_equivalence R).refl,  
          apply (is_congruence.to_is_equivalence R).symm, exact H
        end,
        rwr <- (group_laws _).mul_one g⁻¹, rwr <- (group_laws _).mul_one g'⁻¹,
        rwr <- Group_left_inv_is_right_inv g, rwr <- (group_laws _).mul_assoc, 
        rwr <- (group_laws _).mul_assoc, fapply C.mul_comp, exact rel, 
        apply (is_congruence.to_is_equivalence R).refl } },
    { fapply set.set_quotient.prec, 
      intro g, change ↥G at g, let g_inv := g⁻¹,
      change @monoid.mul (Monoid_cong_quotient R).carrier _ 
               (Monoid_to_Set_functor.map (Monoid_cong_quotient R).is_mon_quot.proj g_inv)
               (Monoid_to_Set_functor.map (Monoid_cong_quotient R).is_mon_quot.proj g) =
               Monoid_to_Set_functor.map (Monoid_cong_quotient R).is_mon_quot.proj _,
      apply λ p, eq.inverse ((monoid_hom_laws 
                             (Monoid_cong_quotient R).is_mon_quot.proj).mul_comp _ _) ⬝ p, 
      rwr (group_laws _).mul_left_inv  } }
end

@[hott]
def conjugate {G : Group} (H : Subgroup G) (g : G) : Subgroup G :=
begin
  fapply Subgroup_of_Subset,
  { intro h', exact ∥Σ (h : G), (h ∈ subset_of_subgroup H) × (g * h * g⁻¹ = h')∥ },
  { fapply subgroup_str.mk,
    { apply tr, fapply dpair, exact 1, fapply prod.mk, exact (subgroup_laws _).one, 
      rwr (group_laws _).mul_one _, exact Group_left_inv_is_right_inv _ },
    { intros g₁ g₂ g₁_el g₂_el, 
      hinduction g₁_el with conj₁, hinduction g₂_el with conj₂,
      hinduction conj₁ with h₁ prod₁, hinduction prod₁ with h₁_el h₁_eq,
      hinduction conj₂ with h₂ prod₂, hinduction prod₂ with h₂_el h₂_eq,
      apply tr, fapply dpair, exact h₁ * h₂, fapply prod.mk,
      exact (subgroup_laws _).mul h₁_el h₂_el, 
      rwr <- (group_laws _).mul_one h₁, rwr <- (group_laws _).mul_left_inv g, 
      rwr <- (group_laws _).mul_assoc _ _ g, rwr (group_laws _).mul_assoc (h₁ * g⁻¹) g h₂,  
      rwr <- (group_laws _).mul_assoc g, rwr <- (group_laws _).mul_assoc g, 
      rwr h₁_eq, rwr (group_laws _).mul_assoc, rwr h₂_eq },
    { intros g₁ g₁_el, hinduction g₁_el with conj, hinduction conj with h prod,
      hinduction prod with h_el h_eq, 
      apply tr, fapply dpair, exact h⁻¹, fapply prod.mk,
      exact (subgroup_laws _).inv h_el, rwr <- h_eq, rwr group_mul_inv, 
      rwr group_mul_inv, rwr group_inv_inv, apply group.mul_assoc } }
end

@[hott]
def is_normal {G : Group} (H : Subgroup G) :=
  Π (g : G), conjugate H g = H

@[hott]
def normal_conj_el {G : Group} {H : Subgroup G} (norm_H : is_normal H) :
  Π (h g : G), h ∈ subset_of_subgroup H -> g * h * g⁻¹ ∈ subset_of_subgroup H :=
begin
  intros h g h_el, 
  have sset : ↥(subset_of_subgroup (conjugate H g) ⊆ subset_of_subgroup H), from 
    begin rwr norm_H g, intros h h_el, exact h_el end,
  change Π h, _ at sset, apply sset, apply tr, fapply fiber.mk,
  { fapply dpair, exact g * h * g⁻¹, apply tr, fapply dpair, exact h, 
    fapply prod.mk, exact h_el, exact idp },
  { exact idp }
end

@[hott]
def conj_el_to_normal {G : Group} {H : Subgroup G} :
  (Π (h g : G), h ∈ subset_of_subgroup H -> g * h * g⁻¹ ∈ subset_of_subgroup H) ->
  is_normal H :=
begin
  intros conj_el g, fapply subobj_antisymm, 
  { apply subgroup_hom_of_subset, intros h' h'_el, hinduction h'_el with fib,
    hinduction fib.1.2 with h_tr h_el_conj, hinduction h_el_conj with h el_conj,
    hinduction el_conj with h_el h_conj, let h'_eq := fib.2, let p := h_conj ⬝ h'_eq,
    rwr <- p, exact conj_el h g h_el },
  { apply subgroup_hom_of_subset, intros h h_el, apply tr, fapply fiber.mk,
    { fapply dpair, exact h, apply tr, fapply dpair, 
      { exact g⁻¹ * h * g },
      { fapply prod.mk,
        { apply cast (ap (λ g', ↥(g⁻¹ * h * g'∈subset_of_subgroup H)) (group_inv_inv g)), 
          exact conj_el h g⁻¹ h_el },
        { rwr <- (group_laws _).mul_assoc g, rwr <- (group_laws _).mul_assoc g,
          rwr Group_left_inv_is_right_inv, rwr (group_laws _).one_mul, 
          rwr (group_laws _).mul_assoc,   
          rwr Group_left_inv_is_right_inv, exact group.mul_one h } } },
    { exact idp } }
end

@[hott]
def subgroup_to_rel {G : Group} (H : Subgroup G) : G -> G -> Prop := 
  λ g h : G, to_Prop (g⁻¹ * h ∈ subset_of_subgroup H)

@[hott, instance]
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
    rwr <- (group_laws _).mul_one g₁⁻¹, rwr <- Group_left_inv_is_right_inv g₂, 
    rwr <- (group_laws _).mul_assoc g₁⁻¹, rwr (group_laws _).mul_assoc _ _ g₃, 
    apply (subgroup_laws _).mul, exact rel₁, exact rel₂ }  
end

@[hott]
def subgroup_rel_cong_to_normal {G : Group} (H : Subgroup G) :
  is_congruence (λ g h : G, subgroup_to_rel H g h) -> is_normal H :=
begin 
  intros is_cong, intro g, fapply subobj_antisymm, 
  { apply subgroup_hom_of_subset, intros h' h'_el, hinduction h'_el with fib,
    hinduction fib.1.2 with h_tr h_el_conj, hinduction h_el_conj with h el_conj,
    hinduction el_conj with h_el h_conj, let h'_eq := fib.2, let p := h_conj ⬝ h'_eq,
    rwr <- p, rwr <- (group_laws _).one_mul (g * h * g⁻¹), rwr group_one_inv_one,
    change ↥(subgroup_to_rel H 1 (g * h * g⁻¹)),  rwr <- Group_left_inv_is_right_inv g,
    fapply is_cong.mul_comp, 
    { rwr <- (group_laws _).mul_one g, fapply is_cong.mul_comp,
      { rwr (group_laws _).mul_one, apply (subgroup_rel_is_equiv _).refl },
      { rwr <- (group_laws _).one_mul h at h_el, rwr group_one_inv_one at h_el, exact h_el } }, 
    { apply (subgroup_rel_is_equiv _).refl } },
  { apply subgroup_hom_of_subset, intros h h_el, apply tr, fapply fiber.mk,
    { fapply dpair, exact h, apply tr, fapply dpair, 
      { exact g⁻¹ * h * g },
      { fapply prod.mk, 
        { rwr <- (group_laws _).one_mul (g⁻¹ * h * g), rwr group_one_inv_one,
          change ↥(subgroup_to_rel H 1 (g⁻¹ * h * g)), 
          rwr <- (group_laws _).mul_left_inv g, fapply is_cong.mul_comp,
          { rwr <- (group_laws _).mul_one g⁻¹, fapply is_cong.mul_comp, 
            { rwr (group_laws _).mul_one, apply (subgroup_rel_is_equiv _).refl },
            { change ↥G at h, rwr <- (group_laws _).one_mul h at h_el, 
              rwr group_one_inv_one at h_el, exact h_el }},
          { apply (subgroup_rel_is_equiv _).refl } },
        { rwr <- (group_laws _).mul_assoc g, rwr <- (group_laws _).mul_assoc g,
          rwr Group_left_inv_is_right_inv, rwr (group_laws _).one_mul, 
          rwr (group_laws _).mul_assoc, change ↥G at h,  
          rwr Group_left_inv_is_right_inv, exact group.mul_one h } } },
    { exact idp } }
end

@[hott, instance]
def normal_subgroup_to_cong_rel {G : Group} (H : Subgroup G) :
    is_normal H -> is_congruence (λ g h : G, subgroup_to_rel H g h) :=
begin
  intro norm_H, 
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
      change ↥(g₂⁻¹ * _ * _ ∈ _), fapply normal_conj_el norm_H, exact rel₁ },
    { exact rel₂ } }
end

@[hott]
def cong_rel_to_normal_subgroup {G : Group} {R : G -> G -> Prop} :
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
        { rwr (group_laws _).one_mul,
          apply @is_equivalence.symm _ (λ g h, R g h) equiv, exact g_el } } } },
  { apply conj_el_to_normal, intros h g h_el, apply tr, fapply fiber.mk,
    { fapply dpair, exact g * h * g⁻¹, change ↥(R (g * h * g⁻¹) 1), 
      rwr <- Group_left_inv_is_right_inv g, fapply cong.mul_comp,
      { rwr <- (group_laws _).mul_one g, rwr (group_laws _).mul_assoc g, 
        rwr (group_laws _).one_mul h, fapply cong.mul_comp,
        { exact @is_equivalence.refl _ (λ g h, R g h) equiv g },
        { hinduction h_el with fib, 
          have p : fib.1.1 = h, from fib.2, rwr <- p, exact fib.1.2 } },
      { exact @is_equivalence.refl _ (λ g h, R g h) equiv g⁻¹ } },
    { exact idp } } 
end 

end algebra

end hott