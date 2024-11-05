import categories.concrete

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.precategories hott.categories

/- To minimize the proof obligations for the defining property of a concrete category we 
   introduce extensions of concrete categories. 
   
   The extra conditions that make a homomorphism of the underlying objects to a homomorphism of 
   the concrete type are collected in an `extra_hom_system`, satisfying the same properties
   than the conditions of a `concrete_hom_system`. The extension of the concrete category is then 
   obtained by intersecting these conditions with the conditions defining homomorphisms in the 
   concrete category. -/
@[hott]
class extra_hom_system {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X) :=
  (hom : Π c d : C, Subset (g (f c) ⟶ g (f d)))
  (id : ∀ c : C, 𝟙 (g (f c)) ∈ hom c c)
  (comp : ∀ {c d e : C} {h₁ : g (f c) ⟶ g (f d)} {h₂ : g (f d) ⟶ g (f e) }, 
            (h₁ ∈ hom c d) -> (h₂ ∈ hom d e) -> h₁ ≫ h₂ ∈ hom c e)
  (inv : ∀ {c d : C} (h : g (f c) ⟶ g (f d)) (hih : is_iso h), (h ∈ hom c d) -> 
                                                               (hih.inv ∈ hom d c))

@[hott, instance]
def extended_hom_system {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : concrete_hom_system (g ∘ f) :=
concrete_hom_system.mk 
  (λ c₁ c₂ : C, extra_hom_system.hom f g c₁ c₂ ∩ @concrete_hom_system.hom D _ g _ (f c₁) 
                                                                                   (f c₂)) 
  (λ c : C, (elem_inter_iff _ _ (𝟙 (g (f c)))).2 ⟨extra_hom_system.id f g c, 
                                                  @concrete_hom_system.id D _ g _ (f c)⟩) 
  (λ c d e h₁ h₂ h₁_el h₂_el, (elem_inter_iff _ _ (h₁ ≫ h₂)).2 
                            ⟨extra_hom_system.comp ((elem_inter_iff _ _ _).1 h₁_el).1 
                                                   ((elem_inter_iff _ _ _).1 h₂_el).1, 
                             concrete_hom_system.comp ((elem_inter_iff _ _ _).1 h₁_el).2 
                                                      ((elem_inter_iff _ _ _).1 h₂_el).2⟩) 
  (λ c d h hih h_el, (elem_inter_iff _ _ hih.inv).2 
                       ⟨extra_hom_system.inv h hih ((elem_inter_iff _ _ _).1 h_el).1, 
                        concrete_hom_system.inv h hih ((elem_inter_iff _ _ _).1 h_el).2⟩)

@[hott, instance]
def has_hom_fib_of_ext_hom_sys {C D : Type _} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : 
  Π {x : X}, has_hom (fiber (g ∘ f) x) :=
@concrete_fib_has_hom _ _ (g ∘ f) (extended_hom_system f g)

@[hott, instance]
def cat_struct_rel_fib {C D : Type _} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : 
  Π {x : X}, category_struct (fiber (g ∘ f) x) := by apply_instance

@[hott, instance]
def rel_fib_has_hom {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] : 
  Π (d : D), has_hom (fiber f d) :=
λ x, has_hom.mk (λ c₁ c₂, to_Set (Σ (h : c₁.1 ⟶ c₂.1), (h.1 : g (f c₁.1) ⟶ g (f c₂.1)) = 
                                       (idtoiso (ap g c₁.2)).hom ≫ (idtoiso (ap g c₂.2⁻¹)).hom))

@[hott]
def rel_fib_hom_eq {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {d : D} {c₁ c₂ : fiber f d} : 
  Π {h₁ h₂ : c₁ ⟶ c₂}, (h₁.1.1 : g (f c₁.1) ⟶ g (f c₂.1)) = h₂.1.1 -> h₁ = h₂ :=
begin 
  intros h₁ h₂ hom_eq, fapply sigma.sigma_eq,
  { fapply sigma.sigma_eq, exact hom_eq, apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }  
end

@[hott, instance]
def rel_fib_cat_struct {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :
  Π (d : D), category_struct (fiber f d) :=
begin
  intro x, fapply category_struct.mk,
  { intro c, fapply dpair, exact 𝟙 c.1, 
    change 𝟙 (g (f c.1)) = _, rwr idtoiso_comp_eq, rwr <- ap_con, rwr con.right_inv },
  { intros a b c h₁ h₂, fapply dpair, exact h₁.1 ≫ h₂.1,
    have ph₁ : h₁.1.1 = _, from h₁.2,
    have ph₂ : h₂.1.1 = _, from h₂.2,
    change h₁.1.1 ≫ h₂.1.1 = _, rwr ph₁, rwr ph₂, 
    rwr is_precat.assoc (idtoiso (ap g a.point_eq)).hom, 
    rwr <-is_precat.assoc (idtoiso (ap g b.point_eq⁻¹)).hom,
    rwr idtoiso_comp_eq, rwr <- ap_con, rwr con.left_inv, 
    rwr ap_idp, rwr idtoiso_refl_eq, 
    change _ ≫ 𝟙 _ ≫ _ = _, rwr is_precat.id_comp }
end

@[hott, instance]
def rel_fib_is_precat {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :
  Π (d : D), is_precat (fiber f d) :=
begin
  intro d, fapply is_precat.mk,
  { intros c₁ c₂ h, fapply sigma.sigma_eq,
    { change 𝟙 c₁.1 ≫ h.1 = _, rwr @is_precat.id_comp _ _ c₁.1 c₂.1 h.1 },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros c₁ c₂ h, fapply sigma.sigma_eq,
    { change h.1 ≫ 𝟙 c₂.1 = _, rwr is_precat.comp_id },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros a b c d₁ h₁ h₂ i, fapply sigma.sigma_eq,
    { change (h₁.1 ≫ h₂.1) ≫ i.1 = h₁.1 ≫ h₂.1 ≫ i.1, 
      rwr @is_precat.assoc _ (concrete_is_precat (g ∘ f)) },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } 
end

@[hott]
class rel_fibs_are_cat {C D : Type _} {X : Category.{u' v}} (f : C -> D) (g : D -> X)
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :=
(homtoid : ∀ {d : D} {c₁ c₂ : fiber f d}, (c₁ ⟶ c₂) -> (c₁ = c₂))
(idhom_to_idp : ∀ {d : D} (c : fiber f d), homtoid (𝟙 c) = idp)

@[hott]
def rel_fib_hom_to_iso {C D : Type _} {X : Category.{u' v}} {f : C -> D} {g : D -> X}
  [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] :
  ∀ {d : D} {c₁ c₂ : fiber f d}, (c₁ ⟶ c₂) -> (f c₁.1 ≅ f c₂.1) :=
λ d c₁ c₂ h, iso_comp (idtoiso c₁.2) (idtoiso c₂.2⁻¹)

@[hott]
def rel_idhom_to_idp {C D : Type _} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [concrete_fibs_are_cat g] 
  [hs_f : extra_hom_system f g] [rfc : rel_fibs_are_cat f g] : 
  ∀ {d : D} (c : fiber f d) (h : c ⟶ c), h = 𝟙 c -> rel_fibs_are_cat.homtoid h = idp := 
begin intros d c h p, rwr p, exact rel_fibs_are_cat.idhom_to_idp g c end

@[hott]
def comp_fib_hom_to_fib_hom {C D : Type _} {X : Category.{u' v}} {f : C -> D}
  {g : D -> X} [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {x : X} : 
  Π {c₁ c₂ : fiber (g ∘ f) x}, (c₁ ⟶ c₂) -> 
                             ((fiber.mk (f c₁.1) c₁.2) ⟶ (fiber.mk (f c₂.1) c₂.2)) :=
begin 
  intros c₁ c₂ h, fapply dpair, 
  { fapply dpair, exact h.1.1, exact ((elem_inter_iff _ _ _).1 h.1.2).2 },
  { exact h.2 }
end

@[hott]
def comp_fib_hom_to_rel_fib_hom {C D : Type _} {X : Category.{u' v}} {f : C -> D}
  {g : D -> X} [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {x : X} : 
  Π {c₁ c₂ : fiber (g ∘ f) x} (p : f c₁.1 = f c₂.1) 
           (q : c₁.point_eq ⬝ c₂.point_eq⁻¹ = ap g p), (c₁ ⟶ c₂) -> 
                             (fiber.mk c₁.1 p ⟶ (fiber.mk c₂.1 idp)) :=
begin 
  intros c₁ c₂ p q h, fapply dpair,
  { fapply dpair, exact h.1.1, exact h.1.2 },
  { change h.1.1 = (idtoiso (ap g p)).hom ≫ (idtoiso (eq.inverse idp)).hom,
    have r : h.1.1 = _, from h.2, rwr r,  
    rwr idtoiso_comp_eq, rwr idtoiso_comp_eq, apply ap iso.hom, apply ap idtoiso,
    assumption }
end

@[hott]
def comp_fib_id_to_rel_fib_id {C D : Type _} {X : Category.{u' v}} {f : C -> D}
  {g : D -> X} [hs_g : concrete_hom_system g] [hs_f : extra_hom_system f g] {x : X} : 
  Π (c : fiber (g ∘ f) x), 
  comp_fib_hom_to_rel_fib_hom idp (eq.con.right_inv c.point_eq) (𝟙 c) = 𝟙 (fiber_comp c).2 :=
begin intro c, apply rel_fib_hom_eq, exact idp end

@[hott, instance]
def rel_fib_cat_to_concrete_fibs_cat {C D : Type _} {X : Category.{u' v}} (f : C -> D) 
  (g : D -> X) [hs_g : concrete_hom_system g] [concrete_fibs_are_cat g] 
  [hs_f : extra_hom_system f g] [rfc : rel_fibs_are_cat f g] : 
  concrete_fibs_are_cat (g ∘ f) :=
begin
  fapply concrete_fibs_are_cat.mk, 
  { intros x c₁ c₂ h,
    apply λ p, (fib_comp_fib_eq c₁) ⬝ p ⬝ (fib_comp_fib_eq c₂)⁻¹, 
    fapply comp_fib_eq, 
    { apply concrete_fibs_are_cat.homtoid, exact comp_fib_hom_to_fib_hom h },
    { apply @ap _ _ fiber.point (@fiber.mk _ _ f (f c₂.1) c₁.1 (ap fiber.point 
                 (concrete_fibs_are_cat.homtoid (comp_fib_hom_to_fib_hom h)))) _, 
      apply @rel_fibs_are_cat.homtoid _ _ _ _ _ hs_g hs_f rfc, 
      fapply comp_fib_hom_to_rel_fib_hom, 
      exact eq.inverse (fiber_ap_ap _ _), exact h },
    { apply eq.concat (idp_con _), apply eq.inverse, apply eq.concat (con_idp _), 
      apply eq.concat (fiber_ap_ap f _), apply eq.concat (con_idp _), exact idp } },
  { intros x c, change fib_comp_fib_eq c ⬝ _ ⬝ (fib_comp_fib_eq c)⁻¹ = _, 
    apply con_inv_eq_of_eq_con, rwr idp_con (fib_comp_fib_eq c), 
    apply con_eq_of_eq_inv_con, rwr con.left_inv, 
    have r : (concrete_fibs_are_cat.homtoid (comp_fib_hom_to_fib_hom (𝟙 c))) = idp, from
      concrete_fibs_are_cat.idhom_to_idp _, rwr r, 
    have q : eq.inverse (fiber_ap_ap g idp) = 
                     con.right_inv (fiber.mk (f c.point) c.point_eq).point_eq, from 
        begin change eq.inverse (eq.inverse (con.right_inv _)) = _, rwr eq.inv_inv end,
    rwr q,
    have q₁ : rel_fibs_are_cat.homtoid (@comp_fib_hom_to_rel_fib_hom _ _ _ f g _ _ _ c c 
            (ap fiber.point (@idp _ (fiber.mk (f c.point) c.point_eq)))
            (con.right_inv (fiber.mk (f c.point) c.point_eq).point_eq) (𝟙 c)) = idp, from 
    begin
      apply rel_idhom_to_idp, 
      change (comp_fib_hom_to_rel_fib_hom idp (con.right_inv c.2) (𝟙 c)) = _,  
      rwr comp_fib_id_to_rel_fib_id c
    end, 
    rwr q₁, change comp_fib_eq f g idp idp _ = idp,
    apply comp_fib_eq_idp_idp, change idp ⬝ _ = eq.inverse idp, 
    apply eq.concat (idp_con _), apply ap eq.inverse, exact idp } 
end


end hott
