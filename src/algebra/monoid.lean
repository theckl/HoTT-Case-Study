import hott.algebra.group hott.arity sets.subset categories.sets categories.concrete
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
def has_hom_eqv_hom (A : Set.{u}) : has_mul A ≃ (A -> A -> A) :=
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
@[hott]
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
                                      (λ A : Set.{u}, has_hom_eqv_hom A)

@[hott]
def Magma_sigma_mul_forget_pr1_htpy : Π (M : Magma), 
  Magma_forget M = sigma.fst (Magma_sigma_mul_equiv.to_fun M) :=
begin 
  intro M, hsimp, rwr sigma.sigma_equiv_sigma_right_fst_eq _ (Magma_sigma_equiv M)
end

@[hott, instance]
def Magma_obj_system : concrete_obj_system Magma_forget 
       (λ A : Set_Category.{u}, A.carrier -> A.carrier -> A.carrier) :=
concrete_obj_system.mk (concrete_equiv.mk Magma_sigma_mul_equiv 
                                          Magma_sigma_mul_forget_pr1_htpy)

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
def has_mul_is_set {A : Type _} [is_set A] : is_set (has_mul A) :=
begin
  fapply @is_trunc_equiv_closed (A -> A -> A) _ 0,
  { fapply equiv.mk,
    { intro mul, exact has_mul.mk mul },
    { fapply adjointify,
      { intro hm, exact @has_mul.mul _ hm },
      { intro hm, hinduction hm, exact idp },
      { intro mul, exact idp } } },
  { apply_instance }
end

@[hott]
def Magma_forget_fib_equiv_pr1_fib (A : Set.{u}) :
  fiber Magma_forget A ≃ fiber (@sigma.fst.{u+1 u} _ (λ A : Set, has_mul A)) A :=
begin
  fapply equiv.mk,
  { intro M_fib, fapply fiber.mk, 
    { exact ⟨M_fib.1.carrier, M_fib.1.struct⟩ },
    { exact M_fib.2 } },
  { fapply adjointify,
    { intro s_fib, fapply fiber.mk,
      { exact Magma.mk s_fib.1.1 s_fib.1.2 },
      { exact s_fib.2 } },
    { intro s_fib, hinduction s_fib with s s_eq, hinduction s with s1 s2, exact idp },
    { intro M_fib, hinduction M_fib with M M_eq, hinduction M with Mc Mh, exact idp } }
end

/- Fibers are sets. -/
@[hott, instance]
def Magma_forget_fib_is_set {A : Set} : concrete_fibs_are_set Magma_forget :=
begin
  apply concrete_fibs_are_set.mk, intro A,
  fapply is_trunc_equiv_closed_rev 0 (Magma_forget_fib_equiv_pr1_fib A), 
  fapply is_trunc_equiv_closed_rev 0, exact fiber.fiber_pr1 (λ A : Set, has_mul A) A,
  exact has_mul_is_set
end

/- Fibers are categories. -/
@[hott]
def Magma_sigma_equiv_id {A : Set_Category} {mul₁ mul₂ : A.carrier → A.carrier → A.carrier}
  (hA : (dpair A mul₁).fst ⟶ (dpair A mul₂).fst) (h_eq : hA = 𝟙 A): 
  (concrete_full_hom_equiv (concrete_equiv_inv (concrete_obj_system.fib_eqv 
                Magma_forget (λ (A : ↥Set_Category), A.carrier → A.carrier → 
                                                        A.carrier)))).map hA = 𝟙 A :=
begin
  change ↥((dpair A mul₁).fst ⟶ (dpair A mul₁).fst) at hA,
  change hA = 𝟙 (dpair A mul₁).fst at h_eq, rwr h_eq
end                                                        

@[hott, instance]
def Magma_fibs_are_cat : 
  sigma_fibs_are_cat (λ A : Set_Category, A.carrier -> A.carrier -> A.carrier) :=
begin
  fapply sigma_fibs_are_cat.mk, 
  { intros A mul₁ mul₂ h, 
    hinduction h with h h_eq, hinduction h with hA hA_pred,
    change ∀ a b : A.carrier, (concrete_full_hom_equiv (concrete_equiv_inv
                (concrete_obj_system.fib_eqv Magma_forget
                (λ (A : ↥Set_Category), A.carrier → A.carrier → A.carrier)))).map hA 
                (mul₁ a b) = _ at hA_pred,
    apply eq_of_homotopy2, intros a b,
    change (𝟙 A : A.carrier -> A.carrier) (mul₁ a b) = 
              mul₂ ((𝟙 A : A.carrier -> A.carrier) a) ((𝟙 A : A.carrier -> A.carrier) b),
    rwr <- Magma_sigma_equiv_id, rwr hA_pred a b },
  { intros A mul, exact is_prop.elim _ _, exact h_eq }
end

@[hott, instance]
def Magma_is_cat : is_cat Magma :=
  @concrete_type_with_obj_sys_is_cat _ _ Magma_forget 
    (λ A : Set_Category, A.carrier -> A.carrier -> A.carrier) _ _ Magma_fibs_are_cat

@[hott]
def Magma_Category : Category :=
  Category.mk Magma Magma_is_cat 

/- Semigroups form a subcategory of magmas. We use the mechanism in [categories.concrete]
   to produce an instance of semigroups being a category. -/
@[hott]
def Semigroup_eqv_Magma_mul_assoc : 
  Semigroup ≃ Σ (M : Magma), Π (a b c : M.carrier), (a * b) * c = a * (b * c) :=
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

@[hott, hsimp]
def Semigroup.to_Magma : Semigroup -> Magma := 
begin
  intro SG, hinduction SG with SG SG_struct, 
  hinduction SG_struct with is_set_SG mul_SG mul_assoc,
  exact Magma.mk (Set.mk SG is_set_SG) (has_mul.mk mul_SG)
end

@[hott]
def Semigroup_Magma_mul_assoc_proj_comm : 
  Semigroup.to_Magma = sigma.fst ∘ Semigroup_eqv_Magma_mul_assoc :=
begin
  apply eq_of_homotopy, intro SG, hinduction SG with SG SG_struct, 
  hinduction SG_struct with is_set_SG mul_SG mul_assoc, exact idp
end

@[hott]
def Semigroup_to_Magma_fib : Π (M : Magma), 
  fiber Semigroup.to_Magma M ≃ Π (a b c : M.carrier), (a * b) * c = a * (b * c) :=
begin  
  rwr Semigroup_Magma_mul_assoc_proj_comm, intro M,
  exact fiber.equiv_precompose sigma.fst Semigroup_eqv_Magma_mul_assoc M ⬝e 
  fiber.fiber_pr1 _ M 
end

@[hott, instance]
def Semigroup_to_Magma_is_inj : is_injective Semigroup.to_Magma :=
begin
  sorry
end

/- `mul_hom A B` are the homomorphisms in the category of `Magma`s. -/
@[hott]
structure mul_hom (A : Type _) (B : Type _) [has_mul A] [has_mul B] 
  [is_set A] [is_set B] :=
  (to_fun : A -> B)
  (map_mul : ∀ a₁ a₂ : A, to_fun (a₁ * a₂) = (to_fun a₁) * (to_fun a₂)) 

@[hott]
instance mul_hom_to_fun (A : Type _) (B : Type _) [has_mul A] [has_mul B] 
  [is_set A] [is_set B] : has_coe_to_fun (mul_hom A B) :=
⟨λ _, A -> B, λ m, m.to_fun⟩

@[hott]
structure semigroup_hom (A : Type _) (B : Type _) [hott.algebra.semigroup A] 
  [hott.algebra.semigroup B] :=
(to_mul_hom : mul_hom A B)

@[hott]
structure monoid_hom (A : Type _) (B : Type _) [hott.algebra.monoid A] 
  [hott.algebra.monoid B] :=
(to_semigroup_hom : semigroup_hom A B)
(map_one : to_semigroup_hom.to_mul_hom 1 = 1)

@[hott]
structure comm_monoid_Hom (A : Type _) (B : Type _) 
  [hott.algebra.comm_monoid A] [hott.algebra.comm_monoid B] :=
(to_monoid_hom : monoid_hom A B)

end algebra

end hott