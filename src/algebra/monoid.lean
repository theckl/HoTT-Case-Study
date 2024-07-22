import hott.algebra.group hott.arity sets.subset categories.sets

universes u u' v w
hott_theory

namespace hott
open is_trunc hott.algebra hott.eq precategories categories hott.is_equiv 
     categories.sets

namespace algebra

/- Building on the algebraic hierarchy in [hott.algebra] we introduce 
   homomorphisms of algebraic structures and show that they form 
   categories. -/

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
structure Magma := 
  (carrier : Set.{u})
  (struct : has_mul carrier)

@[hott] 
instance has_coe_to_sort_Magma : has_coe_to_sort Magma := 
  ⟨_, Magma.carrier⟩
 
attribute [instance] Magma.struct   

@[hott] 
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
def mul_hom_is_set (A B : Magma.{u}) : is_set (mul_hom A.carrier B.carrier) :=
@subset.inj_to_Set_is_set.{u u} (mul_hom A.carrier B.carrier) 
          (set.to_Set.{u} (A.carrier -> B.carrier)) mul_hom.to_fun 
          (mul_hom_to_fun_is_inj A.carrier B.carrier) 

@[hott]
instance Magma_has_hom : has_hom Magma.{u}  :=
  has_hom.mk (λ A B : Magma, Set.mk (mul_hom A.carrier B.carrier) 
                                    (mul_hom_is_set A B))

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
  (Σ (p : A.carrier = B.carrier), A.struct =[ap trunctype.carrier p] B.struct) ≃ 
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

@[hott]
def Magma_isoequivid (A B : Magma.{u}) : (A = B) ≃ (A ≅ B) :=
begin
  sorry 
end

@[hott]
def Magma_idtoiso {A B : Magma.{u}} : 
  (Magma_isoequivid A B).to_fun = idtoiso :=
begin
  fapply eq_of_homotopy, intro p, hinduction p, rwr idtoiso_refl_eq,
  sorry
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