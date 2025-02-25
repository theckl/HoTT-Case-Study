import algebra.ring.module 
       
universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets

namespace algebra

@[hott]  --[GEVE]
def zero_Module (R : CommRing) : Module R :=
begin  
  fapply Module.mk One, 
  fapply module.mk,
  { exact unit_AbGroup.struct },
  { intros r m, exact m },
  { intro m, exact idp },
  { intros r s m, exact idp },
  { intros r m n, exact idp },
  { intros r s m, change m = @ab_group.mul _ unit_AbGroup.struct m m, 
    hinduction m, exact @ab_group.mul_one _ unit_AbGroup.struct _ }
end

notation `[0]_` R := zero_Module R

@[hott]
def initial_mod_hom {R : CommRing} (M : Module R) : ([0]_R) ⟶ M :=
begin 
  fapply module_hom.mk,
  { intro o, exact 0 },
  { fapply module_hom_str.mk, 
    { intros o₁ o₂, rwr (module_laws M).add_zero },
    { exact idp },
    { intros r o, rwr scal_mul_zero_zero } } 
end

@[hott]
def initial_mod_hom_is_unique {R : CommRing} (M : Module R) : 
  Π (f g : ([0]_R) ⟶ M), f = g :=
begin 
  intros f g, fapply Module_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro o, 
  have p : Π (o : ([0]_R)), o = 0, from 
    begin intro o, hinduction o, exact idp end,
  rwr p o, exact eq.concat (module_hom_laws f).zero_comp (module_hom_laws g).zero_comp⁻¹
end

@[hott]
def terminal_mod_hom {R : CommRing} (M : Module R) : M ⟶ ([0]_R) :=
begin 
  fapply module_hom.mk,
  { intro m, exact 0 },
  { fapply module_hom_str.mk, 
    { intros m₁ m₂, rwr (module_laws ([0]_R)).add_zero },
    { exact idp },
    { intros r m, rwr scal_mul_zero_zero } } 
end

@[hott]
def terminal_mod_hom_is_unique {R : CommRing} (M : Module R) : 
  Π (f g : M ⟶ ([0]_R)), f = g :=
begin 
  intros f g, fapply Module_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro m, 
  have p : Π (o : ([0]_R)), o = 0, from 
    begin intro o, hinduction o, exact idp end,
  rwr p ((Module_to_Set_functor R).map g m), rwr p ((Module_to_Set_functor R).map f m) 
end

/- Direct sums of finitely many R-modules satisfy the universal properties of both 
   products and sums resp. coproducts. -/
@[hott]
structure is_direct_sum_module {R : CommRing} (SM : Module R) {n : ℕ} 
  (M : tuple (Module R) n) :=
(set_prod : is_cons_set_tuple_product (λi : fin n, set.to_Set (M i)) (set.to_Set SM))
(proj_hom : Π (i : fin n), module_hom_str (λ m, (set_prod.gens m).1 i))

@[hott]
def direct_sum_module {R : CommRing} {n : ℕ} (M : tuple (Module R) n) : Module R :=
begin
  fapply Module.mk (Π (i : fin n), M i), 
  fapply module.mk,
  { exact (direct_sum_of_AddAbGroups (tuple.map Module.to_AddAbGroup M)).struct' },
  { intros r m i, exact (M i).struct.scal_mul r (m i) },
  { intro m, apply eq_of_homotopy, intro i, exact (M i).struct.one_scal_mul (m i) },
  { intros r s m, apply eq_of_homotopy, intro i, 
    exact (M i).struct.scal_mul_assoc r s (m i) },
  { intros r m n, apply eq_of_homotopy, intro i, 
    exact (M i).struct.left_distr r (m i) (n i) },
  { intros r s m, apply eq_of_homotopy, intro i, 
    exact (M i).struct.right_distr r s (m i) }
end

@[hott]
def direct_sum_module_is_direct_sum {R : CommRing} {n : ℕ} (M : tuple (Module R) n) : 
  is_direct_sum_module (direct_sum_module M) M :=
begin
  fapply is_direct_sum_module.mk, 
  { fapply is_cons_set_tuple_product.mk,
    { exact id },
    { intro m, exact ⟨m, idp⟩ },
    { intros s t p, exact p } },
  { intro i, fapply module_hom_str.mk,
    { intros m n, exact idp },
    { exact idp },
    { intros r m, exact idp } }
end

@[hott]
structure is_module_product {R : CommRing} (P : Module R) {n : ℕ} 
  (M : tuple (Module R) n) :=
(proj : Π (i : fin n), P ⟶ M i)
(factors : Π {Q : Module R} (q : Π (i : fin n), Q ⟶ M i), 
                                      Σ (h : Q ⟶ P), Π (i : fin n), q i = h ≫ proj i)
(unique : Π {Q : Module R} (h₁ h₂ : Q ⟶ P), 
                                (Π (i : fin n), h₁ ≫ proj i = h₂ ≫ proj i) -> h₁ = h₂)

@[hott]
def direct_sum_proj_hom {R : CommRing} {n : ℕ} (M : tuple (Module R) n) (j : fin n) :
  (direct_sum_module M) ⟶ M j :=
begin 
  fapply module_hom.mk,
  { intro m, exact m j },
  { exact (direct_sum_module_is_direct_sum M).proj_hom j }
end

@[hott]
def direct_sum_proj_hom_eq {R : CommRing} {n : ℕ} (M : tuple (Module R) n) (j : fin n) :
  Π (m : direct_sum_module M), 
                     (Module_to_Set_functor R).map (direct_sum_proj_hom M j) m = m j :=
begin
  intro m, change (Module_to_Set_functor R).map (module_hom.mk _ _) _ = _, exact idp
end

@[hott]
def direct_sum_of_modules_is_product {R : CommRing} {n : ℕ} (M : tuple (Module R) n) : 
  is_module_product (direct_sum_module M) M :=
begin
  fapply is_module_product.mk,
  { intro i, exact direct_sum_proj_hom M i },
  { intros Q q, fapply dpair,
    { fapply module_hom.mk, 
      { intros m i, exact (Module_to_Set_functor R).map (q i) m },
      { fapply module_hom_str.mk,
        { intros n₁ n₂, apply eq_of_homotopy, intro i, 
          exact (module_hom_laws (q i)).add_comp _ _ },
        { apply eq_of_homotopy, intro i, exact (module_hom_laws (q i)).zero_comp },
        { intros r m, apply eq_of_homotopy, intro i, 
          exact (module_hom_laws (q i)).scal_mul_comp _ _ } } },
    { intro i, apply Module_to_Set_functor_is_faithful, exact idp } },
  { intros Q h₁ h₂ comp_eq, apply Module_to_Set_functor_is_faithful,
    apply ((set_tuple_product_equiv_univ _ _).1 
               ((is_cons_equiv_is_set_tuple_product _ _).1 
                               (direct_sum_module_is_direct_sum M).set_prod)).unique,
    intro i, apply eq_of_homotopy, intro m,
    exact ap10 (ap (precategories.functor.map (Module_to_Set_functor R)) (comp_eq i)) m }
end

@[hott]
structure is_module_sum {R : CommRing} (S : Module R) {n : ℕ} 
  (M : tuple (Module R) n) :=
(inj : Π (i : fin n), M i ⟶ S)
(factors : Π {T : Module R} (q : Π (i : fin n), M i ⟶ T), 
                                      Σ (h : S ⟶ T), Π (i : fin n), q i = inj i ≫ h)
(unique : Π {T : Module R} (h₁ h₂ : S ⟶ T), 
                                (Π (i : fin n), inj i ≫ h₁ = inj i ≫ h₂) -> h₁ = h₂)

@[hott]
def direct_summand_hom {R : CommRing} {n : ℕ} (M : tuple (Module R) n) : 
  Π (i : fin n), M i ⟶ (direct_sum_module M) :=  
begin
  intro i, fapply module_hom.mk,
  { intros m j, exact dite (i = j) (λ p, p ▸ m) (λ np, 0) },
  { fapply module_hom_str.mk,
    { intros m₁ m₂, apply eq_of_homotopy, intro j, 
      change @decidable.rec (i = j) (λ dec, M j) _ _ _ = 
                                  @decidable.rec (i = j) (λ dec, M j) _ _ _ +
                                  @decidable.rec (i = j) (λ dec, M j) _ _ _,
      hinduction (fin.has_decidable_eq i j) with dec p np, 
      { change p ▸ (m₁ + m₂) = p ▸ m₁ + p ▸ m₂, hinduction p, exact idp },
      { change (0 : M j) = 0 + 0, exact ((module_laws (M j)).add_zero 0)⁻¹ } },
    { apply eq_of_homotopy, intro j, 
      change @decidable.rec (i = j) (λ dec, M j) _ _ _ = 0, 
      hinduction (fin.has_decidable_eq i j) with dec p np,
      { change p ▸ 0 = 0, hinduction p, exact idp },
      { exact idp } },
    { intros r m, apply eq_of_homotopy, intro j, 
      change @decidable.rec (i = j) (λ dec, M j) _ _ _ = 
                                        r ⬝ @decidable.rec (i = j) (λ dec, M j) _ _ _,
      hinduction (fin.has_decidable_eq i j) with dec p np,
      { change p ▸ (r ⬝ m) = r ⬝ (p ▸ m), hinduction p, exact idp },
      { change (0 : M j) = r ⬝ 0, exact (scal_mul_zero_zero (M j) r)⁻¹ } } }
end

@[hott]
def direct_summand_hom_sum_eq {R : CommRing} {n : ℕ} (M : tuple (Module R) n) :
  Π (m : direct_sum_module M), m = 
       module_sum_of_tuple (λ i : fin n, (Module_to_Set_functor R).map 
                                                    (direct_summand_hom M i) (m i)) :=
begin 
  intro m, apply eq_of_homotopy, intro j, 
  rwr <- direct_sum_proj_hom_eq M j (module_sum_of_tuple (λ (i : fin n), 
                        (Module_to_Set_functor R).map (direct_summand_hom M i) (m i))),
  rwr module_sum_of_tuple_hom,
  change _ = module_sum_of_tuple (λ (i : fin n), dite _ _ _),
  apply (λ q, eq.concat (module_sum_of_tuple_comp (m j) j)⁻¹ q),
  apply ap module_sum_of_tuple, apply eq_of_homotopy, intro i, 
  change dite _ _ _ = dite _ _ _, hinduction fin.has_decidable_eq j i with dec p np,
  { hinduction p, change m j = _, hinduction fin.has_decidable_eq j j with dec' q nq,
    { change _ = q ▸ m j, have r : q = idp, from is_set.elim _ _, rwr r },
    { hinduction nq idp } },
  { change (0 : M j) = _, hinduction fin.has_decidable_eq i j with dec' q nq,
    { hinduction np q⁻¹ },
    { exact idp } }
end

@[hott]
def direct_sum_of_modules_is_sum {R : CommRing} {n : ℕ} (M : tuple (Module R) n) : 
  is_module_sum (direct_sum_module M) M :=
begin 
  fapply is_module_sum.mk,
  { intro i, exact direct_summand_hom M i },
  { intros T sum_hom, fapply dpair,
    { fapply module_hom.mk,
      { intro m, exact module_sum_of_tuple 
                       (λ i : fin n, (Module_to_Set_functor R).map (sum_hom i) (m i) ) },
      { fapply module_hom_str.mk,
        { intros m₁ m₂, 
          change module_sum_of_tuple (λ (i : fin n), (Module_to_Set_functor R).map 
                                                          (sum_hom i) (m₁ i + m₂ i)) = _,
          rwr <- module_sum_of_tuples_add, apply ap module_sum_of_tuple,
          apply eq_of_homotopy, intro i, change (Module_to_Set_functor R).map _ _ = _,
          rwr (module_hom_laws (sum_hom i)).add_comp },
        { change _ = (0 : T), rwr <- @module_sum_of_tuples_zero R T n, 
          apply ap module_sum_of_tuple, apply eq_of_homotopy, intro i,
          change (Module_to_Set_functor R).map _ (0 : M i) = 0, 
          exact (module_hom_laws (sum_hom i)).zero_comp },
        { intros r m, rwr <- @module_sum_of_tuples_scal_mul R T n, 
          apply ap module_sum_of_tuple, apply eq_of_homotopy, intro i,
          change (Module_to_Set_functor R).map _ (r ⬝ _) = r ⬝ _, 
          rwr (module_hom_laws (sum_hom i)).scal_mul_comp } } },
    { intro j, apply Module_to_Set_functor_is_faithful,
      rwr (Module_to_Set_functor R).map_comp, apply eq_of_homotopy, intro m,
      change _ = module_sum_of_tuple (λ (i : fin n), (Module_to_Set_functor R).map 
             (sum_hom i) ((Module_to_Set_functor R).map (direct_summand_hom M j) m i)), 
      rwr <- module_sum_of_tuple_comp ((Module_to_Set_functor R).map (sum_hom j) m) j, 
      apply ap module_sum_of_tuple, apply eq_of_homotopy, intro i, 
      change dite _ _ _ = (Module_to_Set_functor R).map _ (dite _ _ _), 
      hinduction fin.has_decidable_eq j i with dec p np,
      { change (Module_to_Set_functor R).map (sum_hom j) m = 
               (Module_to_Set_functor R).map (sum_hom i) (p ▸ m), hinduction p, 
        exact idp },
      { change (0 : T) = (Module_to_Set_functor R).map _ 0, 
        exact (module_hom_laws (sum_hom i)).zero_comp⁻¹ } } },
  { intros T h₁ h₂ sum_hom_eq, apply Module_to_Set_functor_is_faithful,
    apply eq_of_homotopy, intro m, rwr direct_summand_hom_sum_eq M m,
    rwr module_sum_of_tuple_hom h₁, rwr module_sum_of_tuple_hom h₂,
    apply ap module_sum_of_tuple, apply eq_of_homotopy, intro i,
    change ((Module_to_Set_functor R).map _ ≫ (Module_to_Set_functor R).map h₁) (m i) = 
           ((Module_to_Set_functor R).map _ ≫ (Module_to_Set_functor R).map h₂) (m i),
    rwr <- (Module_to_Set_functor R).map_comp, 
    exact ap10 (ap (@precategories.functor.map _ _ _ _ (Module_to_Set_functor R) _ _) 
                                                                (sum_hom_eq i)) (m i) }
end

end algebra

end hott