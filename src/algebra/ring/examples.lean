import algebra.ring.module 
       
universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.relation hott.is_equiv subset precategories 
     categories categories.sets hott.categories.limits hott.categories.colimits 
     hott.categories.strict

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

/- A product of modules indexed by a set and characterised by the universal property of a limit. -/
@[hott]  --[GEVE]
def product_Module {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module_Category R) : 
  Module R :=
begin
  fapply Module.mk (Π (i : I), (M i).carrier), 
  fapply module.mk,
  { exact (direct_product_of_AddAbGroups I (λ (i : I), (Module.to_AddAbGroup (M i)))).struct' },
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
def product_Module_proj {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module_Category R) :
  Π (i : I), product_Module M ⟶ M i :=
begin
  intro i, fapply module_hom.mk,
  { intro m, exact m i },
  { fapply module_hom_str.mk,
    { intros m₁ m₂, exact idp },
    { exact idp },
    { intros r m, exact idp } }
end

@[hott]
def product_Module_cone {R : CommRing.{max u' u}} {J : Set.{u'}} (M : J -> Module_Category R) : 
  cone (discrete.functor M) :=
begin
  fapply cone.mk,
  { exact product_Module M },
  { fapply nat_trans.mk,
    { intro i, 
      have p : (constant_functor (product_Module M)).obj i = product_Module M, from idp,
      rwr p, exact product_Module_proj M i },
    { intros i j f, change i = j at f, hinduction f,
      rwr (constant_functor _).map_id } }
end

@[hott]  --[GEVE]
def product_Module_is_product {R : CommRing.{max u' u}} {J : Set.{u'}}
  (M : J -> Module_Category R) : is_limit (product_Module_cone M) :=
begin 
  fapply is_limit.mk, 
  { intro Q_cone, fapply cone_map.mk,
    { fapply module_hom.mk,
      { intros q i, exact (Module_to_Set_functor R).map (Q_cone.leg i) q },
      { fapply module_hom_str.mk,
        { intros q₁ q₂, apply eq_of_homotopy, intro i, 
          exact (module_hom_laws _).add_comp _ _ },
        { apply eq_of_homotopy, intro i, exact (module_hom_laws _).zero_comp },
        { intros r q, apply eq_of_homotopy, intro i, 
          exact (module_hom_laws _).scal_mul_comp _ _ } } },
    { intro j, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy, intro q,
      exact idp } },
  { intros Q_cone Q_cone_map, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy2,
    intros q i, 
    have p : (Module_to_Set_functor R).map (Q_cone_map.v_lift ≫ 
                                                 ((product_Module_cone M).π.app i)) q = 
             (Module_to_Set_functor R).map Q_cone_map.v_lift q i, from idp,
    rwr <- p, apply λ r, eq.concat (ap10 (ap (@precategories.functor.map _ _ _ _ 
                                  (Module_to_Set_functor R) _ _) (Q_cone_map.fac i)) q) r, 
    exact idp }
end

@[hott, reducible]
def module_Product {J : Set.{u'}} {R : CommRing.{max u' u}} (M : J -> Module_Category R) : 
  limit_cone (discrete.functor M) := 
limit_cone.mk (product_Module_cone M) (product_Module_is_product M)

@[hott, instance]
def module_has_limit {J : Set.{u'}} {R : CommRing.{max u' u}} (M : J -> Module_Category R) :
  has_limit (discrete.functor M) := 
has_limit.mk (module_Product M)

@[hott, instance]
def module_has_product {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module R) :
  has_product M :=
⟨module_has_limit M⟩

/- A direct sum of modules indexed by a set and characterised by the universal property of a 
   colimit. -/
@[hott]
def add_comb_Module_scal_mul {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module_Category R) :
  R -> (add_comb_Monoid (λ (i : ↥I), Module.to_AddAbGroup (M i))) ->
       (add_comb_Monoid (λ (i : ↥I), Module.to_AddAbGroup (M i))) :=
begin
  intros r ac, hinduction ac with i a ac,
  { exact add_comb.zero },
  { exact add_comb.sum (r ⬝ a) ih }
end

@[hott]
def add_comb_Module_scal_mul_add {R : CommRing.{max u' u}} {I : Set.{u'}} 
  (M : I -> Module_Category R) : 
  Π (r : R) (ac₁ ac₂ : add_comb_Monoid (λ (i : ↥I), Module.to_AddAbGroup (M i))), 
  add_comb_Module_scal_mul M r (ac₁ * ac₂) = (add_comb_Module_scal_mul M r ac₁) * 
                                             (add_comb_Module_scal_mul M r ac₂) :=
begin
  intros r ac₁ ac₂, hinduction ac₁ with i a ac₁,
  { exact idp },
  { change add_comb.sum _ (add_comb_Module_scal_mul M r (ac₁ * ac₂)) = 
           add_comb.sum _ (add_comb_Module_scal_mul M r ac₁ * add_comb_Module_scal_mul M r ac₂), 
    rwr ih }
end                                             

@[hott]
def sum_Module_scal_mul {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module_Category R) :
  R -> (direct_sum_of_AddAbGroups.{u u'} (λ i : I, (M i).to_AddAbGroup)).carrier ->
       (direct_sum_of_AddAbGroups.{u u'} (λ i : I, (M i).to_AddAbGroup)).carrier :=
begin
  intro r, fapply set.set_quotient.rec,
  { intro ac, exact set.set_class_of _ (add_comb_Module_scal_mul M r ac)  },
  { intros ac₁ ac₂ H, hinduction H with H, hinduction H with ac₁ ac₂ rel,
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, revert ac₂ rel,
      fapply @add_comb.rec _ _ (λ a, Π {b : add_comb_Monoid (λ i : I, (M i).to_AddAbGroup)}, 
                add_comb_rel (λ i : I, (M i).to_AddAbGroup) a b → 
                cong_sequence (add_comb_rel (λ i : I, (M i).to_AddAbGroup)) 
                (add_comb_Module_scal_mul M r a) (add_comb_Module_scal_mul M r b)), 
      { intros b rel, hinduction rel },
      { intros i a' ac ih, hinduction ac with j a'' bc, 
        { intros bc' rel, hinduction bc' with j b bc',
          { have p : a' = 0, from rel, 
            change cong_sequence (add_comb_rel _) (add_comb.sum (r ⬝ a') add_comb.zero) add_comb.zero,
            fapply @cong_sequence.rel (add_comb_Monoid _), change r ⬝ a' = 0, rwr p, 
            exact scal_mul_zero_zero _ _ },
          { hinduction rel } },
        { intros bc' rel, hinduction bc' with k b bc', 
          { hinduction bc with l b' bc'', hinduction rel, hinduction rel },
          { hinduction bc with l b' bc'',
            { hinduction bc' with m b'' bc''',
              { hinduction rel with p qs, hinduction qs with q s, hinduction p, hinduction q,
                have s' : a' + a'' = b, from s,
                have mul_s : r ⬝ a' + r ⬝ a'' = r ⬝ b, by 
                  rwr <- (module_laws _).left_distr; rwr s', 
                fapply @cong_sequence.rel (add_comb_Monoid _), exact ⟨idp, ⟨idp, mul_s⟩⟩ },
              { hinduction bc''' with n b₃ bc₄, 
                { hinduction rel with p₁ pq, hinduction pq with p₂ q, hinduction q with q₁ q₂,
                  hinduction p₁, hinduction p₂, have q₁' : a' = b'', from q₁, 
                  have q₂' : a'' = b, from q₂, fapply @cong_sequence.rel (add_comb_Monoid _),
                  fapply dpair idp, fapply dpair idp, rwr q₁', rwr q₂', exact ⟨idp, idp⟩ },
                { hinduction rel } } },
            { hinduction rel } } } } },
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, exact cong_sequence.refl _ _ },
    { apply pathover_of_eq, apply eq.inverse, exact eq_of_pathover ih },
    { apply pathover_of_eq, exact (eq_of_pathover ih_r) ⬝ (eq_of_pathover ih_r') },
    { apply pathover_of_eq, rwr add_comb_Module_scal_mul_add, rwr add_comb_Module_scal_mul_add, 
      apply λ p, eq.concat ((monoid_hom_laws (Monoid_quotient.is_mon_quot (Monoid_cong_quotient 
                                               (add_comb_congruence _))).proj).mul_comp _ _) p,  
      apply λ p, eq.concat p (eq.inverse ((monoid_hom_laws (Monoid_quotient.is_mon_quot 
                            (Monoid_cong_quotient (add_comb_congruence _))).proj).mul_comp _ _)),
      apply λ p, eq.concat (ap (λ acl, acl + _) (eq_of_pathover ih_r)) p, 
      apply λ p, eq.concat (ap (λ acl, _ + acl) (eq_of_pathover ih_s)) p, exact idp } }
end

@[hott]  --[GEVE]
def sum_Module {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module_Category R) : 
  Module R :=
begin
  fapply Module.mk,
  { exact (direct_sum_of_AddAbGroups.{u u'} (λ i : I, (M i).to_AddAbGroup)).carrier },  
  { fapply module.mk,
    { exact (direct_sum_of_AddAbGroups.{u u'} (λ i : I, (M i).to_AddAbGroup)).struct' },
    { exact sum_Module_scal_mul M },
    { fapply set.set_quotient.prec, intro ac, apply set.eq_of_setrel, apply tr,
      hinduction ac with i a ac, exact cong_sequence.refl _ _, 
      change cong_sequence (add_comb_rel (λ (i : I), Module.to_AddAbGroup (M i))) 
                           (add_comb.sum ((1:R) ⬝ a) _) _,
      rwr (module_laws _).one_scal_mul, 
      fapply @cong_sequence.mul (add_comb_Monoid _) _ (add_comb.sum a add_comb.zero) 
                                                      (add_comb.sum a add_comb.zero) _ _, 
      exact cong_sequence.refl _ _, exact ih },
    { intros r s, fapply set.set_quotient.prec, intro ac, apply set.eq_of_setrel, apply tr,
      hinduction ac with i a ac, exact cong_sequence.refl _ _, 
      change cong_sequence (add_comb_rel (λ (i : I), Module.to_AddAbGroup (M i))) 
                           (add_comb.sum ((r * s) ⬝ a) _) _,
      rwr (module_laws _).scal_mul_assoc, 
      fapply @cong_sequence.mul (add_comb_Monoid _) _ (add_comb.sum (r ⬝ (s ⬝ a)) add_comb.zero)
                                                      (add_comb.sum (r ⬝ (s ⬝ a)) add_comb.zero) _ _,
      exact cong_sequence.refl _ _, exact ih },
    { intro r, fapply set.set_quotient.prec2, intros ac bc, apply set.eq_of_setrel, apply tr,
      hinduction ac with i a ac, exact cong_sequence.refl _ _, 
      fapply @cong_sequence.mul (add_comb_Monoid _) _ (add_comb.sum (r ⬝ a) add_comb.zero) 
                                                      (add_comb.sum (r ⬝ a) add_comb.zero) _ _, 
      exact cong_sequence.refl _ _, exact ih },
    { intros r s, fapply set.set_quotient.prec, intro ac, apply set.eq_of_setrel, apply tr,
      hinduction ac with i a ac, exact cong_sequence.refl _ _, 
      change cong_sequence (add_comb_rel (λ (i : ↥I), Module.to_AddAbGroup (M i))) 
                           (add_comb.sum _ (add_comb_Module_scal_mul M (r + s) _)) _,
      rwr (module_laws _).right_distr, 
      fapply @cong_sequence.trans (add_comb_Monoid _) _ _ 
               ((add_comb.sum (r ⬝ a) add_comb.zero) * (add_comb.sum (s ⬝ a) add_comb.zero) *
                (add_comb_Module_scal_mul M (r + s) ac)),
      { fapply @cong_sequence.mul (add_comb_Monoid _) _ (add_comb.sum (r ⬝ a + s ⬝ a) add_comb.zero) _
                (add_comb_Module_scal_mul M (r + s) ac) (add_comb_Module_scal_mul M (r + s) ac),
        { fapply cong_sequence.symm _, fapply @cong_sequence.rel (add_comb_Monoid _), 
          exact ⟨idp, ⟨idp, idp⟩⟩ },
        { exact cong_sequence.refl _ _ } },
      { fapply @cong_sequence.trans (add_comb_Monoid _) _ _ 
               ((add_comb.sum (r ⬝ a) add_comb.zero) * (add_comb.sum (s ⬝ a) add_comb.zero) *
                ((add_comb_Module_scal_mul M r ac) * (add_comb_Module_scal_mul M s ac))),
        { fapply @cong_sequence.mul (add_comb_Monoid _) _ 
                ((add_comb.sum (r ⬝ a) add_comb.zero) * (add_comb.sum (s ⬝ a) add_comb.zero)) _
                                                (add_comb_Module_scal_mul M (r + s) ac) _, 
          exact cong_sequence.refl _ _, exact ih },
        { change cong_sequence (add_comb_rel (λ (i : ↥I), Module.to_AddAbGroup (M i)))
            (@monoid.mul (add_comb_Monoid _) _ (@monoid.mul (add_comb_Monoid _) _
                (add_comb.sum (r ⬝ a) add_comb.zero) (add_comb.sum (s ⬝ a) add_comb.zero)) 
                (@monoid.mul (add_comb_Monoid _) _ (add_comb_Module_scal_mul M r ac) 
                                                   (add_comb_Module_scal_mul M s ac)))
            (@monoid.mul (add_comb_Monoid _) _ (@monoid.mul (add_comb_Monoid _) _
                (add_comb.sum (r ⬝ a) add_comb.zero) (add_comb_Module_scal_mul M r ac)) 
                (@monoid.mul (add_comb_Monoid _) _ (add_comb.sum (s ⬝ a) add_comb.zero)
                                                   (add_comb_Module_scal_mul M s ac))), 
          rwr @monoid.mul_assoc (add_comb_Monoid _) _, 
          rwr <- @monoid.mul_assoc (add_comb_Monoid _) _ (add_comb.sum (s ⬝ a) add_comb.zero),
          rwr @monoid.mul_assoc (add_comb_Monoid _) _ (add_comb.sum (r ⬝ a) add_comb.zero),
          rwr <- @monoid.mul_assoc (add_comb_Monoid _) _ _ (add_comb.sum (s ⬝ a) add_comb.zero),
          fapply @cong_sequence.mul (add_comb_Monoid _) _ (add_comb.sum (r ⬝ a) add_comb.zero)
                                                          (add_comb.sum (r ⬝ a) add_comb.zero), 
          { exact cong_sequence.refl _ _ },
          { fapply @cong_sequence.mul (add_comb_Monoid _) (add_comb_rel (λ (i : ↥I), Module.to_AddAbGroup (M i))) 
                ((add_comb.sum (s ⬝ a) add_comb.zero) * (add_comb_Module_scal_mul M r ac))
                ((add_comb_Module_scal_mul M r ac) * (add_comb.sum (s ⬝ a) add_comb.zero)) _ _,
            { exact add_comb_comm_cong_seq _ _ _ },
            { exact cong_sequence.refl _ _ } } } } } }
end

@[hott]
def sum_Module_inj {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module_Category R) :
  Π (i : I), (discrete.functor M).obj i ⟶ sum_Module M :=
begin
  intro i, fapply module_hom.mk,
  { intro m, exact set.set_class_of _ (add_comb.sum m add_comb.zero) },
  { fapply module_hom_str.mk,
    { intros m₁ m₂, apply set.eq_of_setrel, apply tr,
      fapply cong_sequence.symm _, fapply @cong_sequence.rel (add_comb_Monoid _),
      exact ⟨idp, ⟨idp, idp⟩⟩ },
    { apply set.eq_of_setrel, apply tr, fapply @cong_sequence.rel (add_comb_Monoid _),
      exact idp },
    { intros r m, apply set.eq_of_setrel, apply tr, exact cong_sequence.refl _ _ } }
end

@[hott]
def sum_Module_cocone {R : CommRing.{max u' u}} {J : Set.{u'}} (M : J -> Module_Category R) : 
  cocone (discrete.functor M) :=
begin
  fapply cocone.mk,
  { exact sum_Module M },
  { fapply nat_trans.mk,
    { intro i, exact sum_Module_inj M i },
    { intros i j f, hinduction f, rwr is_precat.comp_id (sum_Module_inj M i), 
      exact is_precat.id_comp (sum_Module_inj M i) } }
end

@[hott]
def ac_Module_to_cocone_map {R : CommRing.{max u' u}} {J : Set.{u'}}
  (M : J -> Module_Category R) (Q : cocone (discrete.functor M)) :
  ↥(Monoid_to_Set_functor.obj (add_comb_Monoid (λ (i : ↥J), Module.to_AddAbGroup (M i)))) → 
                                                                                 Q.X.carrier :=
begin
  intro ac, hinduction ac with i a ac,
  { exact 0 },
  { exact (Module_to_Set_functor _).map (Q.π.app i) a + ih }
end

@[hott]
def ac_Module_to_cocone_map_add {R : CommRing.{max u' u}} {J : Set.{u'}}
  {M : J -> Module_Category R} (Q : cocone (discrete.functor M)) :
Π (ac bc : ↥(add_comb_Monoid (λ (i : ↥J), Module.to_AddAbGroup (M i)))), 
  ac_Module_to_cocone_map M Q (ac * bc) = (ac_Module_to_cocone_map M Q ac) +
                                                     (ac_Module_to_cocone_map M Q bc) :=
begin
  intros ac bc, hinduction ac with i a ac,
  { change ac_Module_to_cocone_map M Q bc = 0 + ac_Module_to_cocone_map M Q bc,
    exact ((module_laws _).zero_add (ac_Module_to_cocone_map M Q bc))⁻¹ },
  { apply λ p, eq.concat (ap (λ q, (Module_to_Set_functor _).map (Q.π.app i) a + q) ih) p,
    exact ((module_laws _).add_assoc _ _ _)⁻¹ }
end

@[hott]
def ac_Module_to_cocone_map_scal_mul {R : CommRing.{max u' u}} {J : Set.{u'}}
  {M : J -> Module_Category R} (Q : cocone (discrete.functor M)) :
Π (r : R) (ac : ↥(add_comb_Monoid (λ (i : ↥J), Module.to_AddAbGroup (M i)))), 
  ac_Module_to_cocone_map M Q (add_comb_Module_scal_mul M r ac) = r ⬝ (ac_Module_to_cocone_map M Q ac) :=
begin
  intros r ac, hinduction ac with i a ac,
  { exact (scal_mul_zero_zero _ r)⁻¹ },
  { fapply @eq.concat _ ((Module_to_Set_functor _).map (Q.π.app i) (r ⬝ a) + _) 
                        (r ⬝ ((Module_to_Set_functor _).map (Q.π.app i) a) + 
                           ac_Module_to_cocone_map M Q (add_comb_Module_scal_mul M r ac)) _,
    { rwr (module_hom_laws _).scal_mul_comp _ _ },
    { rwr ih, rwr <- (module_laws _).left_distr } }
end

@[hott]
def sum_Module_to_cocone_map {R : CommRing.{max u' u}} {J : Set.{u'}}
  (M : J -> Module_Category R) (Q : cocone (discrete.functor M)) :
(sum_Module_cocone M).X.carrier → Q.X.carrier :=
begin 
  fapply set.set_quotient.rec, 
  { exact ac_Module_to_cocone_map M Q },
  { intros ac ac' H, apply pathover_of_eq, hinduction H with H, hinduction H,
    { revert b r,
      fapply @add_comb.rec _ _ (λ a, Π {b : add_comb_Monoid _}, add_comb_rel _ a b → 
                               ac_Module_to_cocone_map M Q a = ac_Module_to_cocone_map M Q b), 
      { intros b r, hinduction r },
      { intros i a' ac ih, hinduction ac with j a'' bc, 
        { intros bc' r, hinduction bc' with j b bc',
          { have p : a' = 0, from r, rwr p,
            apply λ q, eq.concat (ap (λ m : Q.X.carrier, m + 0) 
                                     (module_hom_laws (Q.π.app i)).zero_comp) q, 
            exact (module_laws _).add_zero 0 },
          { hinduction r } },
        { intros bc' r, hinduction bc' with k b bc', 
          { hinduction bc with l b' bc'', hinduction r, hinduction r },
          { hinduction bc with l b' bc'',
            { hinduction bc' with m b'' bc''',
              { hinduction r with p qs, hinduction qs with q s, hinduction p, hinduction q,
                have s' : a' + a'' = b, from s, rwr <- s',
                fapply @eq.concat _ _ (((Module_to_Set_functor _).map (Q.π.app j) a' + 
                                        (Module_to_Set_functor _).map (Q.π.app j) a'') + 0) _, 
                { exact ((module_laws _).add_assoc _ _ _)⁻¹ },
                { rwr eq.inverse ((module_hom_laws _).add_comp _ _) } },
              { hinduction bc''' with n b₃ bc₄, 
                { hinduction r with p₁ pq, hinduction pq with p₂ q, hinduction q with q₁ q₂,
                  hinduction p₁, hinduction p₂, have q₁' : a' = b'', from q₁, rwr <- q₁',
                  have q₂' : a'' = b, from q₂, rwr <- q₂',
                  fapply @eq.concat _ _ ((((Module_to_Set_functor _).map (Q.π.app i) a' : Q.X.carrier) + 
                                        ((Module_to_Set_functor _).map (Q.π.app j) a'')) + 0) _,
                  { exact ((module_laws _).add_assoc _ _ _)⁻¹ },
                  { rwr (module_laws _).add_comm ((Module_to_Set_functor _).map (Q.π.app i) a'), 
                    exact (module_laws _).add_assoc _ _ _ } },
                { hinduction r } } },
            { hinduction r } } } } },
    { exact idp },
    { rwr ih },
    { rwr ih_r, exact ih_r' },
    { rwr ac_Module_to_cocone_map_add, rwr ac_Module_to_cocone_map_add,
      rwr ih_r, rwr ih_s } }
end

@[hott]
def sum_Module_to_cocone_hom {R : CommRing.{max u' u}} {J : Set.{u'}}
  (M : J -> Module_Category R) (Q : cocone (discrete.functor M)) :
(sum_Module_cocone M).X ⟶ Q.X :=
begin 
  fapply module_hom.mk,
    { exact sum_Module_to_cocone_map M Q },
    { fapply module_hom_str.mk,
      { fapply set.set_quotient.prec2, intros ac bc, exact ac_Module_to_cocone_map_add _ _ _ },
      { exact idp },
      { intro r, fapply set.set_quotient.prec, intro ac, 
        exact ac_Module_to_cocone_map_scal_mul _ _ _ } }
end

@[hott]  
def sum_Module_is_sum {R : CommRing.{max u' u}} {J : Set.{u'}}
  (M : J -> Module_Category R) : is_colimit (sum_Module_cocone M) :=
begin 
  fapply is_colimit.mk, 
  { intro Q, exact sum_Module_to_cocone_hom M Q },
  { intros Q j, apply Module_to_Set_functor_is_faithful, 
    apply @eq.concat _ _ ((Module_to_Set_functor R).map ((sum_Module_cocone M).π.app j) ≫ 
                          (Module_to_Set_functor R).map (sum_Module_to_cocone_hom M Q)) _, 
    { exact (Module_to_Set_functor R).map_comp _ _ },
    { apply eq_of_homotopy, intro m, exact (module_laws _).add_zero _ } },
  { intros Q s sum_eq, apply Module_to_Set_functor_is_faithful,
    apply eq_of_homotopy, fapply set.set_quotient.prec, intro ac,
    hinduction ac with i a ac,
    { exact (module_hom_laws _).zero_comp },
    { apply @eq.concat _ _ ((Module_to_Set_functor R).map s 
                  (set.set_class_of _ (add_comb.sum a add_comb.zero) + set.set_class_of _ ac)) _,
      { exact idp },
      { apply @eq.concat _ _ ((Module_to_Set_functor R).map s 
                  (set.set_class_of _ (add_comb.sum a add_comb.zero)) + 
                  ((Module_to_Set_functor R).map s (set.set_class_of _ ac))) _,
        { exact (module_hom_laws _).add_comp _ _ },
        { rwr ih, apply @eq.concat _ _ ((((Module_to_Set_functor R).map 
                 ((sum_Module_cocone M).π.app i) ≫ (Module_to_Set_functor R).map s) a) + _) _,        
          { exact idp },
          { fapply @eq.concat _ _ (((Module_to_Set_functor R).map 
                 ((sum_Module_cocone M).π.app i ≫ s) a) + (ac_Module_to_cocone_map M Q ac)) _,
            { rwr (module_laws _).add_comm, 
              rwr (module_laws _).add_comm _ (ac_Module_to_cocone_map M Q ac) },
            { fapply @eq.concat _ _ (((Module_to_Set_functor R).map 
                 (Q.π.app i) a) + (ac_Module_to_cocone_map M Q ac)) _,
              { apply ap (λ q, q + (ac_Module_to_cocone_map M Q ac)), 
                exact ap (λ f, (Module_to_Set_functor R).map f a) (sum_eq i) },
              { exact idp } } } } } } }
end

@[hott, reducible]
def module_Sum {J : Set.{u'}} {R : CommRing.{max u' u}} (M : J -> Module_Category R) : 
  colimit_cocone (discrete.functor M) := 
colimit_cocone.mk (sum_Module_cocone M) (sum_Module_is_sum M)

@[hott, instance]
def module_has_colimit {J : Set.{u'}} {R : CommRing.{max u' u}} (M : J -> Module_Category R) :
  has_colimit (discrete.functor M) := 
has_colimit.mk (module_Sum M)

@[hott, instance]
def module_has_sum {R : CommRing.{max u' u}} {I : Set.{u'}} (M : I -> Module R) :
  has_coproduct M :=
⟨module_has_colimit M⟩ 

/- `R`-algebras are `R`-modules, and the ring homomorphism from `R` is a module 
    homomorphism. -/
@[hott, reducible, instance] 
def module_of_algebra {R : CommRing.{u}} (S : Type u) [H : algebra R S] : 
  module R S :=
begin 
  fapply module.mk,
  { exact @add_ab_group_of_ring S (comm_ring.to_ring S) },
  { intros r s, exact (H.scalar_map r) * s },
  { intro s, apply (λ p, eq.concat (ap (λ t, t * s) H.hom_str.one_comp) p),
    exact comm_ring.one_mul s },
  { intros r₁ r₂ s, apply (λ p, eq.concat (ap (λ t, t * s) (H.hom_str.mul_comp _ _)) p),
    exact comm_ring.mul_assoc _ _ _ },
  { intros r s t, exact comm_ring.left_distrib _ _ _ },
  { intros r s t, apply (λ p, eq.concat (ap (λ t', t' * t) (H.hom_str.add_comp _ _)) p),
    exact comm_ring.right_distrib _ _ _ }
end

@[hott]  --[GEVE]
def Algebra.to_Module {R : CommRing.{u}} : Algebra R -> Module R :=
  λ S, Module.mk S (module_of_algebra S) 

@[hott] --[GEVE]
def ring_Module (R : CommRing.{u}) : Module R :=
  Algebra.to_Module (Algebra.mk' R (𝟙 R))

notation R`^[1]` := ring_Module R

/- The free module over a set `I` is just the direct sum of `I` copies of `R^[1]`. The 
   universal property of freeness is the universal property of a direct sum. -/
@[hott]
def free_Module {R : CommRing.{max u' u}} {I : Set.{u'}} : Module R :=
  copi_obj (λ i : I, R^[1]) 

@[hott]  --[GEVE]
def scalar_to_mod_hom {R : CommRing.{u}} {S : CommRing.{u}} (h : R ⟶ S) : 
  R^[1] ⟶ Algebra.to_Module (Algebra.mk' S h) :=
begin
  fapply module_hom.mk,
  { intro r, exact CommRing_to_Set_functor.map h r },
  { fapply module_hom_str.mk,
    { intros r₁ r₂, exact (comm_ring_hom_laws h).add_comp _ _ },
    { exact (comm_ring_hom_laws h).zero_comp },
    { intros r r', change CommRing_to_Set_functor.map h (r * r') = _, 
      rwr (comm_ring_hom_laws h).mul_comp } }
end

@[hott]  --[GEVE]
def module_pullback {R : CommRing.{u}} {S : CommRing.{u}} (h : R ⟶ S) :
  Module S -> Module R :=
begin
  intro M, fapply Module.mk M, fapply module.mk, 
  { exact M.struct.to_ab_group },
  { intros r m, exact M.struct.scal_mul (CommRing_to_Set_functor.map h r) m },
  { intro m, apply λ p, eq.concat (ap (λ r, M.struct.scal_mul r m) 
                                             (comm_ring_hom_laws h).one_comp) p,
    exact M.struct.one_scal_mul m },
  { intros r r' m, apply λ p, eq.concat (ap (λ r, M.struct.scal_mul r m) 
                                         ((comm_ring_hom_laws h).mul_comp r r')) p,
    change M.struct.scal_mul (_ * _) m = _, rwr M.struct.scal_mul_assoc },
  { intros r m n, exact M.struct.left_distr _ _ _ },
  { intros r r' m, apply λ p, eq.concat (ap (λ r, M.struct.scal_mul r m) 
                                         ((comm_ring_hom_laws h).add_comp r r')) p,
    exact M.struct.right_distr _ _ _ }
end

/- Every additive abelian group has the structure of a ℤ-module. -/
@[hott, reducible]
def int_scal_mul_AddAbGroup {M : AddAbGroup} : ℤ -> M.carrier -> M.carrier :=
begin
  intros a m, hinduction a with n n,
  { hinduction n, exact 0, exact ih + m },
  { hinduction n, exact -m, exact ih - m }
end

@[hott, reducible]
def int_scal_mul_AddAbGroup_succ {M : AddAbGroup} : Π (a : ℤ) (m : M.carrier),
  int_scal_mul_AddAbGroup (a + 1) m = int_scal_mul_AddAbGroup a m + m :=
begin
  intros a m, hinduction a with k k,
  { exact idp },
  { hinduction k,
    { change int_scal_mul_AddAbGroup (- 1 + 1) m = - m + m,
      rwr int.add_left_neg 1, rwr add.left_inv },
    { change int_scal_mul_AddAbGroup (-[1+ n] + (- 1) + 1) m = 
                                           int_scal_mul_AddAbGroup -[1+ n] m + (- m) + m,
      rwr int.add_assoc, rwr int.add_left_neg, rwr int.add_zero, 
      rwr add.assoc, rwr add.left_inv, rwr add_zero } }
end

@[hott, reducible]
def int_scal_mul_AddAbGroup_pred {M : AddAbGroup} : Π (a : ℤ) (m : M.carrier),
  int_scal_mul_AddAbGroup (a + - 1) m = int_scal_mul_AddAbGroup a m - m :=
begin 
  intros a m, hinduction a with k k,
  { hinduction k with k,
    { change int_scal_mul_AddAbGroup (0 + -[1+ 0]) m = 0 + - m, rwr int.zero_add, 
      rwr zero_add },
    { change int_scal_mul_AddAbGroup (int.of_nat k + 1 + - 1) m = 
             int_scal_mul_AddAbGroup (int.of_nat k) m + m + - m,
      rwr int.add_assoc, rwr int.add_comm 1, rwr int.add_left_neg, rwr int.add_zero,
      rwr add.assoc, rwr add.comm m, rwr add.left_inv, rwr add_zero } },
  { exact idp }
end

@[hott]
def int_scal_mul_right_distrib {M : AddAbGroup} : Π (a b : ℤ) (m : M.carrier),
    int_scal_mul_AddAbGroup (a + b) m = 
                       (int_scal_mul_AddAbGroup a m) + (int_scal_mul_AddAbGroup b m) :=
begin
  intros a b m, hinduction b with k k,
  { hinduction k with k,
    { change int_scal_mul_AddAbGroup (a + 0) m = _ + 0, rwr int.add_zero a, rwr add_zero },
    { change int_scal_mul_AddAbGroup (a + (int.of_nat k + 1)) m = 
                            _ + int_scal_mul_AddAbGroup (int.of_nat k + 1) m, 
      rwr <- int.add_assoc a, rwr int_scal_mul_AddAbGroup_succ,
      rwr int_scal_mul_AddAbGroup_succ, rwr <- add.assoc, rwr ih } },
  { hinduction k with k, 
    { change int_scal_mul_AddAbGroup (a + - 1) m = _ + -m, 
      rwr int_scal_mul_AddAbGroup_pred },
    { change int_scal_mul_AddAbGroup (a + (-[1+ k] + - 1)) m = 
                                    _ + int_scal_mul_AddAbGroup (-[1+ k] + - 1) m,
      rwr <- int.add_assoc a, rwr int_scal_mul_AddAbGroup_pred, 
      rwr int_scal_mul_AddAbGroup_pred, change _ = _ + (_ + -m), rwr <- add.assoc, rwr ih } }
end

@[hott]
def int_scal_mul_neg {M : AddAbGroup} : Π (a : ℤ) (m : M.carrier),
    int_scal_mul_AddAbGroup (-a) m = - int_scal_mul_AddAbGroup a m :=
begin 
  intros a m, hinduction a with k k,
  { hinduction k with k,
    { change (0:M.carrier) = -0, rwr neg_zero },
    { change int_scal_mul_AddAbGroup -[1+ k] m = 
             -(int_scal_mul_AddAbGroup (int.of_nat k) m + m), rwr neg_add',rwr <- ih,
      hinduction k with k,
      { change -m = 0 + -m, rwr zero_add },
      { change int_scal_mul_AddAbGroup -[1+ k] m + -m = 
               int_scal_mul_AddAbGroup (-[1+ k]) m + -m, exact idp } } },
  { change int_scal_mul_AddAbGroup (int.of_nat k) m + m = _, 
    hinduction k with k,
    { change 0 + m = - -m, rwr zero_add, rwr neg_neg },
    { change int_scal_mul_AddAbGroup (int.of_nat k) m + m + m = 
             -(int_scal_mul_AddAbGroup -[1+ k] m + -m), rwr ih, rwr neg_add', rwr neg_neg } }
end

@[hott]  --[GEVE]
def AddAbGroup_is_ℤ_module : AddAbGroup -> Module int_Ring :=
begin
  intro M, fapply Module.mk M.carrier, fapply module.mk,
  { exact M.struct' },
  { exact int_scal_mul_AddAbGroup },
  { intro m, change 0 + m = m, exact zero_add m },
  { intros r s m, hinduction r with k k, 
    { hinduction k with k,
      { change int_scal_mul_AddAbGroup (0 * s) m = 0, rwr int.zero_mul },
      { change int_scal_mul_AddAbGroup ((int.of_nat k + 1) * s) m = 
               int_scal_mul_AddAbGroup (int.of_nat k + 1) _, rwr int.distrib_right,
        rwr int.one_mul, rwr int_scal_mul_right_distrib, rwr ih } },
    { hinduction k with k, 
      { change int_scal_mul_AddAbGroup ((- 1 : int_Ring) * s) m = 
               - (int_scal_mul_AddAbGroup s m), rwr <- neg_mul_eq_neg_mul, 
        rwr comm_ring_laws.one_mul, rwr int_scal_mul_neg },
      { change int_scal_mul_AddAbGroup ((-[1+ k] + - 1) * s) m =
               int_scal_mul_AddAbGroup -[1+ k] _ - _, rwr int.distrib_right, 
        rwr int_scal_mul_right_distrib, 
        change _ + int_scal_mul_AddAbGroup ((- 1 : int_Ring) * s) m = _,
        rwr <- neg_mul_eq_neg_mul, rwr comm_ring_laws.one_mul, rwr int_scal_mul_neg, rwr ih } } },
  { intros r m n, hinduction r with k k,
    { change int_scal_mul_AddAbGroup _ (m + n) = _ + _,
      hinduction k with k,
      { change (0 : M.carrier) = 0 + 0, rwr add_zero },
      { change int_scal_mul_AddAbGroup (int.of_nat k) (m + n) + (m + n) =
               (int_scal_mul_AddAbGroup (int.of_nat k) m + m) +
               (int_scal_mul_AddAbGroup (int.of_nat k) n + n),
        rwr ih, rwr add.assoc _ _ (m + n), rwr <- add.assoc _ m n, rwr add.comm _ m, 
        rwr add.assoc m, rwr <- add.assoc _ m _ } },
    { change int_scal_mul_AddAbGroup _ (m + n) = _ + _,
      hinduction k with k,
      { change -(m + n) = -m + -n, rwr neg_add' },
      { change int_scal_mul_AddAbGroup -[1+ k] (m + n) + -(m + n) = 
               (int_scal_mul_AddAbGroup -[1+ k] m + -m) + (_ + -n), rwr neg_add', rwr ih,
        rwr add.assoc _ _ (-m + -n), rwr <- add.assoc _ (-m) (-n), rwr add.comm _ (-m), 
        rwr add.assoc (-m), rwr <- add.assoc _ (-m) _ } } },
  { exact @int_scal_mul_right_distrib M }
end

/- The set of homomorphisms between two R-modules also has the structure of an R-module. -/
@[hott]
def zero_mod_hom {R : CommRing} (M N : Module R) : M ⟶ N :=
begin
  fapply module_hom.mk,
  { intro m, exact 0 },
  { fapply module_hom_str.mk,
    { intros m n, rwr (module_laws N).add_zero },
    { exact idp },
    { intros r m, rwr scal_mul_zero_zero } }
end

@[hott]
def hom_mod_add {R : CommRing} {M N : Module R} : (M ⟶ N) -> (M ⟶ N) -> (M ⟶ N) :=
begin
  intros f g, fapply module_hom.mk, 
  { intro m, exact (Module_to_Set_functor R).map f m + (Module_to_Set_functor R).map g m },
  { fapply module_hom_str.mk,
    { intros m n, rwr (module_hom_laws f).add_comp, rwr (module_hom_laws g).add_comp,
      rwr (module_laws N).add_assoc _ ((Module_to_Set_functor R).map f n) _,
      rwr <- (module_laws N).add_assoc ((Module_to_Set_functor R).map f n),
      rwr (module_laws N).add_comm ((Module_to_Set_functor R).map f n), 
      rwr (module_laws N).add_assoc _ ((Module_to_Set_functor R).map f n) _,
      rwr <- (module_laws N).add_assoc ((Module_to_Set_functor R).map f m) },
    { rwr (module_hom_laws f).zero_comp, rwr (module_hom_laws g).zero_comp,
      change (0:N) + 0 = 0, rwr (module_laws N).add_zero },
    { intros r m, rwr (module_hom_laws f).scal_mul_comp,
      rwr (module_hom_laws g).scal_mul_comp, rwr <- (module_laws N).left_distr }}
end

@[hott]
def hom_mod_neg {R : CommRing} {M N : Module R} : (M ⟶ N) -> (M ⟶ N) :=
begin
  intro f, fapply module_hom.mk,
  { intro m, exact -(Module_to_Set_functor R).map f m },
  { fapply module_hom_str.mk,
    { intros m n, rwr (module_hom_laws f).add_comp, rwr neg_add' },
    { rwr (module_hom_laws f).zero_comp, change -(0:N) = 0, rwr neg_zero },
    { intros r m, rwr (module_hom_laws f).scal_mul_comp, rwr neg_scal_mul_eq_mul_neg } }
end

@[hott]
def scal_mul_hom_mod {R : CommRing} {M N : Module R} : R -> (M ⟶ N) -> (M ⟶ N) :=
begin
  intros r f, fapply module_hom.mk,
  { intro m, exact r ⬝ (Module_to_Set_functor R).map f m },
  { fapply module_hom_str.mk,
    { intros m n, rwr (module_hom_laws f).add_comp, rwr (module_laws N).left_distr },
    { rwr (module_hom_laws f).zero_comp, change r ⬝ (0:N) = (0:N), rwr scal_mul_zero_zero },
    { intros s m, rwr (module_hom_laws f).scal_mul_comp, 
      rwr <- (module_laws N).scal_mul_assoc, rwr comm_ring_laws.mul_comm, 
      rwr (module_laws N).scal_mul_assoc } }
end

@[hott]
def hom_mod_add_ab_group (R : CommRing) (M N : Module R) : add_ab_group (M ⟶ N) :=
begin
  fapply ab_group.mk, 
  { apply_instance },
  { exact hom_mod_add },
  { intros f g h, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change _ + _ + _ = _ + (_ + _), rwr (module_laws N).add_assoc },
  { exact zero_mod_hom M N },
  { intro f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change (0:N) + _ = _, rwr (module_laws N).zero_add },
  { intro f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change _ + (0:N) = _, rwr (module_laws N).add_zero },
  { exact hom_mod_neg },
  { intro f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change - _ + _ = (0:N), rwr (module_laws N).add_left_inv },
  { intros f g, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change _ + _ = _ + _, rwr (module_laws N).add_comm }
end

@[hott]
def hom_Module (R : CommRing) (M N : Module R) : Module R :=
begin
  fapply Module.mk (M ⟶ N), fapply module.mk,
  { exact hom_mod_add_ab_group R M N },
  { exact scal_mul_hom_mod },
  { intro f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change (1:R) ⬝ _ = _, rwr (module_laws N).one_scal_mul },
  { intros r s f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change (r * s) ⬝ _ = r ⬝ (s ⬝ _), rwr (module_laws N).scal_mul_assoc },
  { intros r f g, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change r ⬝ (_ + _) = r ⬝ _ + r ⬝ _, rwr (module_laws N).left_distr },
  { intros r s f, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro m, change (r + s) ⬝ _ = r ⬝ _ + s ⬝ _, rwr (module_laws N).right_distr }
end

@[hott]
def mod_hom_comp {R : CommRing} (N M L : Module R) : 
  hom_Module R N M -> hom_Module R M L -> hom_Module R N L :=
λ f g, f ≫ g

@[hott]
def mod_hom_comp_is_bilinear {R : CommRing} (N M L : Module R) :
  is_bilinear_map (mod_hom_comp N M L) :=
begin
  fapply is_bilinear_map.mk,
  { intros f₁ f₂ g, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro n, change (Module_to_Set_functor R).map (_ ≫ _) _ = 
      (Module_to_Set_functor R).map (f₁ ≫ g) _ + (Module_to_Set_functor R).map (f₂ ≫ g) _, 
    rwr (Module_to_Set_functor R).map_comp, rwr (Module_to_Set_functor R).map_comp,
    rwr (Module_to_Set_functor R).map_comp, 
    change (Module_to_Set_functor R).map _ (_ + _) = (Module_to_Set_functor R).map g _ +
                                                     (Module_to_Set_functor R).map g _, 
    exact (module_hom_laws g).add_comp _ _ },
  { intros r f g, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro n, change (Module_to_Set_functor R).map (_ ≫ _) _ = 
                    r ⬝ (Module_to_Set_functor R).map (_ ≫ _) _, 
    rwr (Module_to_Set_functor R).map_comp, rwr (Module_to_Set_functor R).map_comp,
    change (Module_to_Set_functor R).map g (r ⬝ _) = r ⬝ (Module_to_Set_functor R).map g _,
    rwr (module_hom_laws g).scal_mul_comp _ _ },
  { intros f g₁ g₂, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro n, change (Module_to_Set_functor R).map (_ ≫ _) _ = 
      (Module_to_Set_functor R).map (f ≫ g₁) _ + (Module_to_Set_functor R).map (f ≫ g₂) _, 
    rwr (Module_to_Set_functor R).map_comp },
  { intros r f g, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro n, change (Module_to_Set_functor R).map (_ ≫ _) _ = 
                    r ⬝ (Module_to_Set_functor R).map (_ ≫ _) _, 
    rwr (Module_to_Set_functor R).map_comp }
end

/- An `R`-module `M` is isomorphic to module homonmorphisms `R^[1] ⟶ M`. -/
@[hott]
def mod_to_mod_hom {R : CommRing} (M : Module R) : M -> hom_Module R (R^[1]) M :=
begin
  intro m, fapply module_hom.mk, 
  { intro r, change ↥R at r, exact (r:R) ⬝ m },
  { fapply module_hom_str.mk,
    { intros r₁ r₂, change ↥R at r₁, change ↥R at r₂, 
      change (r₁ + r₂) ⬝ m = r₁ ⬝ m + r₂ ⬝ m, rwr (module_laws M).right_distr },
    { change (0:R) ⬝ m = 0, exact zero_scal_mul_zero M m },
    { intros r s, change ↥R at s, change (r * s) ⬝ m = r ⬝ (s ⬝ m), 
      rwr (module_laws M).scal_mul_assoc } } 
end

@[hott]
def mod_to_mod_hom_str {R : CommRing} (M : Module R) : module_hom_str (mod_to_mod_hom M) :=
begin
  fapply module_hom_str.mk,
  { intros m₁ m₂, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro r, change ↥R at r, change r ⬝ (m₁ + m₂) = r ⬝ m₁ + r ⬝ m₂, 
    exact (module_laws M).left_distr _ _ _ },
  { apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro r, change ↥R at r, change r ⬝ (0:M) = 0, exact scal_mul_zero_zero M r },
  { intros r m, apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
    intro s, change ↥R at s, change s ⬝ (r ⬝ m) = r ⬝ (s ⬝ m), 
    rwr <- (module_laws M).scal_mul_assoc, rwr <- (module_laws M).scal_mul_assoc, 
    rwr comm_ring_laws.mul_comm }
end

@[hott]
def mod_hom_to_mod {R : CommRing} (M : Module R) : hom_Module R (R^[1]) M -> M :=
begin
  intro f, exact (Module_to_Set_functor R).map f (1:R)
end

@[hott]
def mod_hom_to_mod_str {R : CommRing} (M : Module R) : module_hom_str (mod_hom_to_mod M) :=
begin
  fapply module_hom_str.mk,
  { intros f g, exact idp },
  { exact idp },
  { intros r f, exact idp }
end

@[hott]
def mod_hom_iso_mod {R : CommRing} (M : Module R) : (hom_Module R (R^[1]) M) ≅ M :=
begin
  fapply iso.mk,
  { exact module_hom.mk (mod_hom_to_mod M) (mod_hom_to_mod_str M) },
  { fapply is_iso.mk,
    { exact module_hom.mk (mod_to_mod_hom M) (mod_to_mod_hom_str M) },
    { apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
      intro m, rwr (Module_to_Set_functor R).map_comp,
      change mod_hom_to_mod M (mod_to_mod_hom M m) = m, 
      change (Module_to_Set_functor R).map _ _ = _, change (1:R) ⬝ m = m, 
      exact (module_laws M).one_scal_mul m },
    { apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
      intro f, rwr (Module_to_Set_functor R).map_comp,
      change mod_to_mod_hom M ((Module_to_Set_functor R).map f (1:R)) = f,
      apply Module_to_Set_functor_is_faithful, apply eq_of_homotopy,
      intro r, change ↥R at r, change r ⬝ _ = _, 
      rwr <- (module_hom_laws f).scal_mul_comp, 
      apply ap ((Module_to_Set_functor R).map f), exact comm_ring_laws.mul_one r } }
end

end algebra

end hott