import hott.algebra.group hott.arity sets.subset categories.sets categories.rel_conc
       hott.algebra.bundled

universes u u' v w
hott_theory

namespace hott
open is_trunc hott.algebra hott.eq precategories categories hott.is_equiv 
     categories.sets

namespace algebra

/- Building on the algebraic hierarchy in [hott.algebra] we introduce homomorphisms of 
   algebraic structures as extensions of homomorphisms of underlying algebraic structures
   and use the machinery of concrete categories to show that together with the objects, 
   they form categories. 
   
   In more details, we need to construct a homomorphism system over the projection map to 
   the underlying algebraic structure, show that the fibers are a set and that the 
   induced precategory structure on the fibers is actually a category. -/

/- We start with magmas: An underlying set is provided with a multiplication. -/
@[hott]
def has_mul_eqv_mul (A : Set.{u}) : has_mul A ≃ (A -> A -> A) :=
begin
  fapply equiv.mk,
  { intro hm, exact hm.mul },
  { fapply adjointify,
    { intro mul, exact has_mul.mk mul },
    { intro mul, exact idp },
    { intro hm, induction hm, exact idp } }
end

@[hott]
structure Magma := 
  (carrier : Set.{u})
  (struct : has_mul carrier)

@[hott] 
instance has_coe_to_sort_Magma : has_coe_to_sort Magma := 
  ⟨_, Magma.carrier⟩

attribute [instance] Magma.struct   

/- The projection map. -/
@[hott, reducible]
def Magma_forget : Magma -> Set_Category.{u} :=
  Magma.carrier

@[hott, instance]
def Magma_has_mul (A : Magma) : has_mul (Magma_forget A).carrier :=
  A.struct

/- Descriptions of the fibers of `Magma_forget`. -/
@[hott, hsimp] 
def Magma_sigma_equiv : Magma.{u} ≃ Σ (carrier : Set.{u}), has_mul carrier :=
begin
  fapply equiv.mk,
  { intro A, exact ⟨A.carrier, A.struct⟩ },
  { fapply adjointify, 
    { intro AS, exact Magma.mk AS.1 AS.2 },
    { intro AS, hinduction AS, exact idp },
    { intro A, hinduction A, exact idp } }
end

@[hott]
def Magma_sigma_mul_equiv : 
  Magma.{u} ≃ Σ (carrier : Set.{u}), carrier -> carrier -> carrier :=
Magma_sigma_equiv ⬝e sigma.sigma_equiv_sigma_right 
                                      (λ A : Set.{u}, has_mul_eqv_mul A)

@[hott, instance]
def Magma_eq_are_sets : ∀ M₁ M₂ : Magma, is_set (M₁ = M₂) :=
begin 
  apply λ H : is_trunc 1 Magma, @is_trunc_eq Magma 0 H,
  fapply is_trunc_equiv_closed_rev 1 Magma_sigma_mul_equiv, 
  fapply sigma.is_trunc_sigma
end

@[hott]
def Magma_sigma_mul_forget_pr1_htpy : Π (M : Magma), 
  Magma_forget M = sigma.fst (Magma_sigma_mul_equiv M) :=
begin 
  intro M, hsimp, rwr sigma.sigma_equiv_sigma_right_fst_eq _ (Magma_sigma_equiv M)
end

@[hott]
def Magma_sigma_mul_pr1_forget_htpy : Π (M : Σ C : Set, C -> C -> C), 
  sigma.fst M = Magma_forget (Magma_sigma_mul_equiv⁻¹ᶠ M) :=
begin
  intro M, apply λ p, p ⬝ (Magma_sigma_mul_forget_pr1_htpy (Magma_sigma_mul_equiv⁻¹ᶠ M))⁻¹, 
  apply ap sigma.fst, rwr is_equiv.right_inv Magma_sigma_mul_equiv
end

@[hott, instance]
def Magma_obj_system : concrete_obj_system Magma_forget 
       (λ A : Set_Category.{u}, A.carrier -> A.carrier -> A.carrier) :=
concrete_obj_system.mk (concrete_equiv.mk (equiv.symm Magma_sigma_mul_equiv) 
                                          Magma_sigma_mul_pr1_forget_htpy)

/- The homomorphism system over the projection map. -/
@[hott, instance]
def Magma_hom_system : concrete_hom_system.{u u+1} Magma_forget := 
begin 
  fapply concrete_hom_system.mk, 
  { intros A B, intro f, fapply trunctype.mk, 
    { exact ∀ a₁ a₂ : A.carrier, f (a₁ * a₂) = f a₁ * f a₂ }, 
    { apply_instance } },
  { intro A, intros a₁ a₂, exact idp }, 
  { intros A B C g h el_g el_h a₁ a₂, change h (g _) = h (g _) * h (g _), 
    rwr el_g, rwr el_h },
  { intros A B g gih el_g b₁ b₂, 
    change gih.inv ((𝟙 (Magma_forget B) : B.carrier -> B.carrier) b₁ * 
                    (𝟙 (Magma_forget B) : B.carrier -> B.carrier) b₂) = _,
    rwr <- ap10 gih.r_inv b₁, rwr <- ap10 gih.r_inv b₂, change gih.inv (g _ * g _) = _, 
    rwr <- el_g, change (g ≫ gih.inv) _ = _, rwr gih.l_inv }
end

@[hott, instance]
def Magma_fibs_are_cat : 
  sigma_fibs_are_cat (λ A : Set_Category.{u}, A.carrier -> A.carrier -> A.carrier) :=
begin
  fapply sigma_fibs_are_cat.mk, 
  { intros A mul₁ mul₂ h h_eq, 
    hinduction h with h hA_pred,
    apply eq_of_homotopy2, intros a b,
    change (𝟙 A : A.carrier -> A.carrier) (mul₁ a b) = 
              mul₂ ((𝟙 A : A.carrier -> A.carrier) a) ((𝟙 A : A.carrier -> A.carrier) b),
    change h = 𝟙 A at h_eq, rwr <- h_eq, 
    exact hA_pred a b },
  { intros A mul, exact is_prop.elim _ _ }
end

@[hott, instance]
def Magma_is_cat : is_cat Magma.{u} :=
  @concrete_type_with_obj_sys_is_cat _ _ Magma_forget 
    (λ A : Set_Category, A.carrier -> A.carrier -> A.carrier) _ _ Magma_fibs_are_cat

@[hott]
def Magma_Category : Category :=
  Category.mk Magma.{u} Magma_is_cat 

/- We show that semigroups form a category, by constructing `Semigroup` as an extension of
   the concrete category `Magma` over `Set_Category`. -/
@[hott, reducible]
def Semigroup.to_Magma : Semigroup -> Magma :=
begin
  intro SG, hinduction SG with SG SG_struct, 
  hinduction SG_struct with is_set_SG mul_SG mul_assoc,
  exact Magma.mk (Set.mk SG is_set_SG) (has_mul.mk mul_SG)
end

@[hott, reducible]
def Semigroup.to_Set : Semigroup -> Set_Category :=
  Magma_forget ∘ Semigroup.to_Magma 

@[hott, instance]
def Semigroup_extra_hom_system : extra_hom_system Semigroup.to_Magma Magma_forget :=
extra_hom_system.mk (λ SG₁ SG₂, subset.total_Subset _)
                    (λ SG, true.intro)
                    (λ SG₁ SG₂ SG₃ h₁ h₂ h₁_in h₂_in, true.intro)
                    (λ SG₁ SG₂ h h_iso h_in, true.intro)

/- To prove that fibers of `Semigroup.to_Magma` over a given underlying Magma form a 
  category, we show how equality of semigroups follows from equality of the underlying 
  magmas. -/
@[hott]
def Semigroup_eqv_Magma_mul_assoc : 
  Semigroup ≃ Σ (M : Magma.{u}), Π (a b c : M.carrier), (a * b) * c = a * (b * c) :=
begin
  fapply equiv.mk,
  { intro SG, hinduction SG with SG SG_struct, 
    hinduction SG_struct with is_set_SG mul_SG mul_assoc,
    exact dpair (Magma.mk (Set.mk SG is_set_SG) (has_mul.mk mul_SG)) mul_assoc },
  { fapply adjointify,
    { intro M_mul_ass, hinduction M_mul_ass with M mul_assoc, hinduction M with M mul_M,
      hinduction M with M is_set_M, hinduction mul_M with mul_M,
      exact Semigroup.mk M (semigroup.mk is_set_M mul_M mul_assoc) },
    { intro M_mul_ass, hinduction M_mul_ass with M mul_assoc, hinduction M with M mul_M,
      hinduction M with M is_set_M, hinduction mul_M with mul_M, exact idp },
    { intro SG, hinduction SG with SG SG_struct, 
      hinduction SG_struct with is_set_SG mul_SG mul_assoc, exact idp } }
end

@[hott]
def Semigroup_Magma_mul_assoc_proj_fn_eq : 
  Semigroup.to_Magma = sigma.fst ∘ Semigroup_eqv_Magma_mul_assoc :=
begin
  apply eq_of_homotopy, intro SG, hinduction SG with SG SG_struct, 
  hinduction SG_struct with is_set_SG mul_SG mul_assoc, exact idp
end

@[hott]
def Semigroup_eq_of_Magma_eq : ∀ {SG₁ SG₂ : Semigroup}, 
  Semigroup.to_Magma SG₁ = Semigroup.to_Magma SG₂ -> SG₁ = SG₂ :=
begin 
  intros SG₁ SG₂ pM, 
  apply equiv.eq_of_fn_eq_fn Semigroup_eqv_Magma_mul_assoc, 
  { fapply sigma.sigma_eq, 
    { exact (ap10 Semigroup_Magma_mul_assoc_proj_fn_eq SG₁)⁻¹ ⬝ pM ⬝ 
            (ap10 Semigroup_Magma_mul_assoc_proj_fn_eq SG₂) },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
end  

@[hott]
def Semigroup_idp_of_Magma_idp (SG : Semigroup) :
  Semigroup_eq_of_Magma_eq (@idp _ (Semigroup.to_Magma SG)) = idp :=
begin 
  change equiv.eq_of_fn_eq_fn _ _ = idp, rwr con_idp, rwr con.left_inv, 
  apply λ p, p ⬝ (equiv.idp_of_fn_idp_fn Semigroup_eqv_Magma_mul_assoc),
  apply ap (equiv.eq_of_fn_eq_fn Semigroup_eqv_Magma_mul_assoc),
  apply λ p, p ⬝ sigma.sigma_eq_idp_idpo, apply ap (sigma.sigma_eq idp), 
  apply λ p, p ⬝ idpo_of_idp_tr, apply ap pathover_of_tr_eq,
  exact is_prop.elim _ _
end

@[hott]
def Semigroup_eq_of_Magma_eq.left_inv : ∀ {SG₁ SG₂ : Semigroup} 
  (pM : Semigroup.to_Magma SG₁ = Semigroup.to_Magma SG₂), 
  ap Semigroup.to_Magma (Semigroup_eq_of_Magma_eq pM) = pM :=
begin
  intros SG₁ SG₂ pM, change ap _ (equiv.eq_of_fn_eq_fn _ _) = _, 
  rwr ap_fn_eq Semigroup_Magma_mul_assoc_proj_fn_eq, 
  rwr ap_compose sigma.fst Semigroup_eqv_Magma_mul_assoc,
  rwr equiv.ap_eq_of_fn_eq_fn, change _ ⬝ (sigma.sigma_eq _ _)..1 ⬝ _ = _, 
  rwr sigma.sigma_eq_fst, rwr con.assoc5, rwr con.right_inv, rwr con.right_inv,
  rwr idp_con
end

@[hott, instance]
def Semigroup_to_Magma_fibs_are_cat : rel_fibs_are_cat Semigroup.to_Magma Magma_forget :=
begin 
  fapply rel_fibs_are_cat.mk, 
  { intros M sg_ext₁ sg_ext₂ h,
    fapply fiber.fiber_eq, 
    { exact Semigroup_eq_of_Magma_eq (sg_ext₁.point_eq ⬝ sg_ext₂.point_eq⁻¹) },
    { apply eq_con_of_con_inv_eq, exact (Semigroup_eq_of_Magma_eq.left_inv _)⁻¹ } },
  { intros M sg_ext, change fiber.fiber_eq _ _ = _, 
    apply λ p, p ⬝ fiber_eq_idp _ _, fapply apd011 fiber.fiber_eq, 
    { apply eq.concat (ap Semigroup_eq_of_Magma_eq (con.right_inv sg_ext.point_eq)), 
      exact Semigroup_idp_of_Magma_idp sg_ext.point },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

@[hott, instance]
def Semigroup_is_cat : is_cat Semigroup :=
begin 
  apply λ c : concrete_fibs_are_cat _, @concrete_fib_cat_to_concrete_cat _ _ (Magma_forget ∘ Semigroup.to_Magma) _ c,
  exact rel_fib_cat_to_concrete_fibs_cat _ _ 
end

@[hott]
def Semigroup_Category : Category :=
  Category.mk Semigroup.{u} Semigroup_is_cat

/- Monoids extend semigroups by a one-element satisfying the usual laws. -/
@[hott, hsimp]
def Monoid_eqv_Semigroup_one_laws : Monoid ≃ 
  Σ (SG : Semigroup) (one : SG), (Π (m : SG), (one * m = m)) × (Π (m : SG), (m * one = m)) :=
begin
  fapply equiv.mk,
  { intro M, hinduction M with M M_struct, hinduction M_struct, 
    fapply dpair, fapply Semigroup.mk M, exact semigroup.mk is_set_carrier mul mul_assoc,
    fapply dpair, exact one, fapply pair, exact one_mul, exact mul_one },
  { fapply adjointify,
    { intro SG_struct, hinduction SG_struct with SG mon_struct, hinduction SG with SG, 
      hinduction struct, hinduction mon_struct with one laws, 
      hinduction laws with one_mul mul_one, fapply Monoid.mk SG, 
      exact monoid.mk is_set_carrier mul mul_assoc one one_mul mul_one },
    { intro SG_struct, hinduction SG_struct with SG mon_struct, hinduction SG with SG, 
      hinduction struct, hinduction mon_struct with one laws, 
      hinduction laws with one_mul mul_one, exact idp },
    { intro M, hinduction M with M M_struct, hinduction M_struct, exact idp } }  
end

@[hott, reducible, hsimp]
def Monoid.to_Semigroup : Monoid -> Semigroup_Category :=
  λ M, Semigroup.mk M (monoid.to_semigroup M)

@[hott, reducible, instance]
def Monoid_hom_system : concrete_hom_system Monoid.to_Semigroup :=
begin
  fapply concrete_hom_system.mk,
  { intros M N h, fapply @trunctype.mk -1, 
    exact h.1 1 = 1, apply_instance },
  { intro M, exact idp },
  { intros M₁ M₂ M₃ f g f_el g_el, change g.1 (f.1 1) = 1, 
    change f.1 1 = 1 at f_el, rwr f_el, change g.1 1 = 1 at g_el, rwr g_el },
  { intros M N g g_iso g_el, change g_iso.inv.1 1 = 1, change g.1 1 = 1 at g_el,
    rwr <- g_el, change (g ≫ g_iso.inv).1 1 = 1, rwr g_iso.l_inv }
end

@[hott]
def Monoid_eq_of_Semigroup_one_eq (M N : Monoid) :
  Π (q : Monoid.to_Semigroup M = Monoid.to_Semigroup N), 
    (@idtoiso _ Semigroup_is_cat.to_is_precat _ _ q).hom.1 1 = 1 -> M = N :=
begin
  sorry
end

@[hott, instance]
def Monoid_fibs_are_cat : concrete_fibs_are_cat Monoid.to_Semigroup :=
begin
  fapply concrete_fibs_are_cat.mk,
  { intros SG M_fib N_fib h_fib, fapply fiber.fiber_eq,
    { fapply Monoid_eq_of_Semigroup_one_eq, 
      { sorry },
      { sorry } },
    { sorry } },
  { sorry }
end

@[hott, instance]
def Monoid_is_cat : is_cat Monoid := by apply_instance

/-
@[hott, reducible]
def Monoid.to_Set : Monoid -> Set_Category := 
  Semigroup.to_Set ∘ Monoid.to_Semigroup

@[hott]
def Monoid_hom.to_map {M N : Monoid} : 
  (Monoid.to_Set M ⟶ Monoid.to_Set N) -> (M.carrier -> N.carrier) :=
begin
  intro f, hinduction M with M M_struct, hinduction N with N N_struct, 
  hinduction M_struct, hinduction N_struct, exact f
end

@[hott]
def Monoid_eq_of_Semigroup_one_eq (M N : Monoid) :
  Π (q : Monoid.to_Semigroup M = Monoid.to_Semigroup N), 
    Monoid_hom.to_map (idtoiso (ap Semigroup.to_Set q)).hom (has_one.one M) = 
                                                             has_one.one N -> M = N :=
begin
  hinduction M with M M_struct, hinduction N with N N_struct,
  intros q one_map, 
  hinduction M_struct, hinduction N_struct, 
  change Semigroup.mk _ _ = Semigroup.mk _ _ at q,
  have p : M = N := ap Semigroup.carrier q, 
  
  hinduction p, 
  fapply apd011, exact idp, apply pathover_idp_of_eq,
  sorry
end 

@[hott]
def Monoid_hom_to_map_comp {M₁ M₂ M₃ : Monoid} 
  (f : Semigroup.to_Set (Monoid.to_Semigroup M₁) ⟶ Semigroup.to_Set (Monoid.to_Semigroup M₂))
  (g : Semigroup.to_Set (Monoid.to_Semigroup M₂) ⟶ Semigroup.to_Set (Monoid.to_Semigroup M₃)) :
  Π (x : M₁.carrier), 
    Monoid_hom.to_map (f ≫ g) x = Monoid_hom.to_map g (Monoid_hom.to_map f x) :=   
begin
  intro x,
  hinduction M₁ with M₁ M_struct₁, hinduction M_struct₁,
  hinduction M₂ with M₂ M_struct₂, hinduction M_struct₂, 
  hinduction M₃ with M₃ M_struct₃, hinduction M_struct₃,
  exact idp
end  

@[hott]
def Monoid_sigma_forget_pr1 : Π (M : Monoid), 
  Monoid.to_Semigroup M = sigma.fst (Monoid_eqv_Semigroup_one_laws.to_fun M) :=
begin 
  intro M, hinduction M with M M_struct, hinduction M_struct, sorry 
end

@[hott, instance]
def Monoid_extra_hom_system : extra_hom_system Monoid.to_Semigroup Semigroup.to_Set :=
begin
  fapply extra_hom_system.mk,
  { intros M N f, fapply @trunctype.mk -1, 
    exact (Monoid_hom.to_map f) 1 = 1, apply_instance },
  { intro M, hinduction M with M M_struct, hinduction M_struct, exact idp },
  { intros M₁ M₂ M₃ f g f_mon g_mon, 
    hinduction M₁ with M₁ M_struct₁, hinduction M_struct₁,
    hinduction M₂ with M₂ M_struct₂, hinduction M_struct₂, 
    hinduction M₃ with M₃ M_struct₃, hinduction M_struct₃,
    change (Monoid_hom.to_map f) 1 = 1 at f_mon, 
    change (Monoid_hom.to_map g) 1 = 1 at g_mon,
    change (Monoid_hom.to_map g (Monoid_hom.to_map f 1)) = 1, 
    rwr f_mon, exact g_mon },
  { intros M₁ M₂ f f_iso f_mon, 
    hinduction M₁ with M₁ M_struct₁, hinduction M_struct₁,
    hinduction M₂ with M₂ M_struct₂, hinduction M_struct₂, 
    change (Monoid_hom.to_map f) 1 = 1 at f_mon,
    change (Monoid_hom.to_map f_iso.inv) 1 = 1, rwr <- f_mon, 
    rwr <- Monoid_hom_to_map_comp, rwr f_iso.l_inv }
end

@[hott, instance]
def Monoid_rel_fibs_are_cat : rel_fibs_are_cat Monoid.to_Semigroup Semigroup.to_Set :=
begin
  fapply rel_fibs_are_cat.mk,
  { intros S mon_S₁ mon_S₂ f, 
    hinduction mon_S₁ with M₁ S_eq₁, hinduction mon_S₂ with M₂ S_eq₂,
    fapply fiber.fiber_eq, 
    { fapply Monoid_eq_of_Semigroup_one_eq,
      { apply @category.isotoid Semigroup_Category, exact rel_fib_hom_to_iso f },
      { sorry } },
    { sorry } },
  { sorry }  
end

@[hott, instance]
def Monoid_is_cat : is_cat Monoid :=
begin 
  apply λ c : concrete_fibs_are_cat _, 
      @concrete_fib_cat_to_concrete_cat _ _ (Semigroup.to_Set ∘ Monoid.to_Semigroup) _ c,
  exact rel_fib_cat_to_concrete_fibs_cat _ _ 
end
-/

end algebra

end hott