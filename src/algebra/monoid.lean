import hott.algebra.group hott.arity sets.subset categories.sets categories.concrete

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

@[hott]
def Magma_sigma_mul_forget_pr1_eq : 
  Magma_forget = sigma.fst ∘ Magma_sigma_mul_equiv.to_fun :=
eq_of_homotopy Magma_sigma_mul_forget_pr1_htpy

@[hott]
def Magma_fib_eqv_mul : Π (A : Set.{u}), fiber Magma_forget A ≃ (A -> A -> A) :=
begin  
  intro A, 
  have g : fiber Magma_forget A ≃ fiber (@sigma.fst Set (λ A, A -> A -> A)) A, from
  begin 
    rwr Magma_sigma_mul_forget_pr1_eq, 
    exact fiber.equiv_precompose sigma.fst Magma_sigma_mul_equiv A 
  end,
  have h : fiber (@sigma.fst Set (λ A, A -> A -> A)) A ≃ (A -> A -> A), from
    fiber.fiber_pr1 _ _,   
  exact g ⬝e h
end

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
@[hott, instance]
def Magma_forget_fib_is_cat : concrete_fibs_are_cat.{u u+1} Magma_forget :=
begin
  fapply concrete_fibs_are_cat.mk, 
  { intros A M N f, 
    hinduction M with M M_eq, hinduction M with B mul_B,
    change B = A at M_eq, hinduction M_eq,
    hinduction N with N N_eq, hinduction N with C mul_C, 
    change C = B at N_eq, hinduction N_eq,
    fapply fiber.fiber_eq,
    { hsimp, fapply apd011 Magma.mk idp, sorry },
    { sorry } },
  { intros, sorry }
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

/- Magma homomorphisms are determined by the underlying map of sets. This 
   will show that the forgetful functor to sets is faithful, but first of 
   all that Magma homomorphisms are sets. -/
@[hott]
def mul_hom_to_fun_is_inj (A : Type _) (B : Type _) [has_mul A] [has_mul B] 
  [is_set A] [is_set B] :
  ∀ m₁ m₂ : mul_hom A B, m₁.to_fun = m₂.to_fun -> m₁ = m₂ :=
begin
  intros m₁ m₂ fun_eq,
  hinduction m₁, hinduction m₂,
  fapply apd011, exact fun_eq, 
    apply pathover_of_tr_eq, apply eq_of_homotopy2, intros a₁ a₂, 
    exact is_prop.elim _ _
end 

@[hott]
class is_mul_hom {A : Type _} {B : Type _} [has_mul A] [has_mul B] 
  [is_set A] [is_set B] (f : A → B) :=
  (map_mul' : ∀ a₁ a₂ : A, f (a₁ * a₂) = f a₁ * f a₂)

@[hott]
instance mul_hom.is_mul_hom {A : Type _} {B : Type _} [has_mul A] [has_mul B] 
  [is_set A] [is_set B] (m : mul_hom A B) : is_mul_hom m :=
is_mul_hom.mk m.map_mul

@[hott]
def map_mul {A : Type _} {B : Type _} [has_mul A] [has_mul B] 
  [is_set A] [is_set B] (f : A → B) [is_mul_hom f] : 
  ∀ a₁ a₂ : A, f (a₁ * a₂) = f a₁ * f a₂ :=
is_mul_hom.map_mul' f

@[hott]
def is_mul_hom.to_mul_hom (A : Type _) (B : Type _) [has_mul A] [has_mul B] 
  [is_set A] [is_set B] (f : A -> B) [is_mul_hom f] : mul_hom A B :=
mul_hom.mk f (map_mul f)

@[hott]
def mul_hom_is_set (A B : Magma.{u}) : is_set (mul_hom A.carrier B.carrier) :=
@subset.inj_to_Set_is_set.{u u} (mul_hom A.carrier B.carrier) 
          (set.to_Set.{u} (A.carrier -> B.carrier)) mul_hom.to_fun 
          (mul_hom_to_fun_is_inj A.carrier B.carrier) 

@[hott]
instance Magma_has_hom : has_hom Magma.{u} :=
  has_hom.mk (λ A B : Magma, Set.mk (mul_hom A.carrier B.carrier) 
                                    (mul_hom_is_set A B))

@[hott]
def Magma_map_eq_to_hom_eq {A B : Magma.{u}} : 
  ∀ (f g : A ⟶ B), mul_hom.to_fun f = mul_hom.to_fun g -> f = g :=
begin
  intros f g p_fun, hinduction f with f map_mul_f, hinduction g with g map_mul_g,
  fapply apd011, exact p_fun, 
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott]
def Magma_id_hom (A : Magma) : A ⟶ A :=
  mul_hom.mk (set.id_map A.carrier) (λ a₁ a₂, idp)

@[hott]
def Magma_comp_hom {A B C : Magma} : (A ⟶ B) -> (B ⟶ C) -> (A ⟶ C) :=
begin  
  intros f g,
  apply mul_hom.mk (g ∘ f),
  intros a₁ a₂, 
  change g.to_fun (f.to_fun _) = g (f _) * g (f _),
  rwr f.map_mul, rwr g.map_mul
end

@[hott, instance]
def Magma_cat_struct : category_struct Magma.{u} :=
  category_struct.mk (λ A : Magma, Magma_id_hom A) @Magma_comp_hom

@[hott, instance]
def Magma_is_precat : is_precat Magma.{u} :=
begin
  apply is_precat.mk,
    intros A B f, apply mul_hom_to_fun_is_inj, refl,
    intros A B f, apply mul_hom_to_fun_is_inj, refl,
    intros A B C D f g h, apply mul_hom_to_fun_is_inj, refl
end  

@[hott]
def Magma_comp_eq_equiv_iso {A B : Magma.{u}} :
  (Σ (p : A.carrier = B.carrier), A.struct =[p; λ (a : Set), has_mul ↥a] B.struct) ≃ 
  (Σ (i : A.carrier ≅ B.carrier), (∀ a₁ a₂ : A.carrier, 
    (i.hom : A.carrier -> B.carrier) (a₁ * a₂) = (i.hom a₁) * (i.hom a₂))) :=
begin
  fapply equiv.mk,  
  { intro p_comp, hinduction p_comp with p q, fapply dpair, 
    { exact idtoiso p },
    { hinduction A with A mul_hom_A, hinduction B with B mul_hom_B, 
      change A = B at p, hinduction p, intros a₁ a₂, 
      hinduction (eq_of_pathover_idp q), exact idp } },
  { fapply adjointify,
    { intro i_comp, hinduction i_comp with i i_mul, fapply dpair,
      { exact categories.sets.Set_isotoid i },
      { hinduction A with A mul_hom_A, hinduction B with B mul_hom_B,
        change A ≅ B at i, hinduction (Set_isotoid i) with p,
        have q : i = id_iso A, from 
          (Set_id_iso_rinv i)⁻¹ ⬝ (ap idtoiso p) ⬝ idtoiso_refl_eq A, 
        apply pathover_idp_of_eq, 
        hinduction mul_hom_A with mul_A, hinduction mul_hom_B with mul_B,
        apply ap has_mul.mk, apply eq_of_homotopy2, 
        rwr q at i_mul, exact i_mul } },
    { intro i_comp, fapply sigma.sigma_eq, 
      { hinduction i_comp with i i_mul, exact Set_id_iso_rinv i },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intro p_comp, fapply sigma.sigma_eq,
      { hinduction p_comp with p struct_eq, exact Set_id_iso_linv p },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end

@[hott, hsimp]
def Magma_comp_idp_to_id_iso {A : Magma.{u}} : 
  @Magma_comp_eq_equiv_iso A A ⟨idp, idpo⟩ = 
                           ⟨id_iso A.carrier, λ a₁ a₂ : A.carrier, idp⟩ :=
begin
  fapply sigma.sigma_eq,
  { exact idp },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

@[hott]
def Magma_comp_iso_equiv_iso {A B : Magma.{u}} :
  (Σ (i : A.carrier ≅ B.carrier), (∀ a₁ a₂ : A.carrier, 
    (i.hom : A.carrier -> B.carrier) (a₁ * a₂) = (i.hom a₁) * (i.hom a₂))) 
    ≃ (A ≅ B) :=
begin
  fapply equiv.mk, 
  { intro i_comp, fapply iso.mk,
    { exact ⟨i_comp.1.hom, i_comp.2⟩ },
    { fapply is_iso.mk,
      { fapply mul_hom.mk,
        { exact i_comp.1.ih.inv },
        { intros b₁ b₂, 
          change i_comp.fst.ih.inv ((𝟙 B.carrier : B.carrier -> B.carrier) b₁ * 
                                (𝟙 B.carrier : B.carrier -> B.carrier) b₂) = _,
          rwr <- (ap10 i_comp.1.ih.r_inv b₁), rwr <- (ap10 i_comp.1.ih.r_inv b₂),
          change i_comp.fst.ih.inv (i_comp.fst.hom _ * i_comp.fst.hom _) = _,
          rwr <- i_comp.2 (i_comp.fst.ih.inv b₁) _, 
          change (i_comp.fst.hom ≫ i_comp.fst.ih.inv) _ = _,
          rwr i_comp.1.ih.l_inv } },
      { apply Magma_map_eq_to_hom_eq _ _, exact i_comp.1.ih.r_inv },
      { apply Magma_map_eq_to_hom_eq _ _, exact i_comp.1.ih.l_inv } } },
  { fapply adjointify,
    { intro i, fapply dpair,
      { fapply iso.mk,
        { exact i.hom.1 },
        { fapply is_iso.mk,
          { exact i.ih.inv.1 },
          { change (i.ih.inv ≫ i.hom).to_fun = _, rwr i.ih.r_inv },
          { change (i.hom ≫ i.ih.inv).to_fun = _, rwr i.ih.l_inv } } },
      { intros a₁ a₂, exact i.hom.2 a₁ a₂ } },
    { intro i, apply hom_eq_to_iso_eq, apply Magma_map_eq_to_hom_eq, exact idp },
    { intro i_comp, hinduction i_comp with i mul_map, fapply sigma.sigma_eq, 
      { apply hom_eq_to_iso_eq, exact idp },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end

@[hott, hsimp]
def Magma_comp_id_iso_to_id_iso {A : Magma.{u}} :
  @Magma_comp_iso_equiv_iso A A ⟨id_iso A.carrier, λ a₁ a₂ : A.carrier, idp⟩ =
    id_iso A :=
begin
  apply hom_eq_to_iso_eq, apply Magma_map_eq_to_hom_eq, exact idp
end

@[hott, hsimp]
def Magma_isoequivid (A B : Magma.{u}) : (A = B) ≃ (A ≅ B) :=
  equiv.eq_equiv_fn_eq_of_equiv Magma_sigma_equiv A B ⬝e 
  (sigma.sigma_eq_equiv _ _) ⬝e
  Magma_comp_eq_equiv_iso ⬝e Magma_comp_iso_equiv_iso ⬝e equiv.rfl

@[hott, hsimp]
def equiv.idp_equiv_fn_idp_of_equiv {A B : Type (u+1)} (f : A ≃ B) 
  (a : A) : equiv.eq_equiv_fn_eq_of_equiv f a a idp = idp :=
idp

set_option pp.universes true

@[hott]
def Magma_idtoiso {A B : Magma.{u}} : 
  (Magma_isoequivid A B).to_fun = idtoiso :=
begin
  fapply eq_of_homotopy, intro p, hinduction p, rwr idtoiso_refl_eq, 
  change equiv.rfl.to_fun (Magma_comp_iso_equiv_iso.to_fun 
    (Magma_comp_eq_equiv_iso.to_fun ⟨idp, idpo⟩)) = equiv.rfl.to_fun (id_iso A), 
  apply ap equiv.rfl.to_fun, rwr <- Magma_comp_id_iso_to_id_iso,
  apply ap Magma_comp_iso_equiv_iso.to_fun, rwr <- Magma_comp_idp_to_id_iso 
end

@[hott, instance]
def Magma_is_cat : is_cat Magma.{u} :=
  is_cat.mk (λ A B, Magma_idtoiso ▸ ((Magma_isoequivid A B).to_is_equiv))

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