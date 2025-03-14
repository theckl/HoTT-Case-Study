import algebra.group.basic
       

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.is_equiv subset precategories categories categories.sets

namespace algebra

/- We show that Abelian groups form a concrete category over the concrete category 
   `Group`, as a full subcategory. -/
@[hott, reducible]
def AbGroup.to_Group : AbGroup.{u} -> Group_Category :=
  λ G, Group.mk G (ab_group.to_group G)

@[hott, reducible]
def AbGroup.mk' (G : Group.{u}) (mul_comm : Π (a b : G.carrier), a * b = b * a) :
  AbGroup :=
AbGroup.mk G.carrier (ab_group.mk G.struct.is_set_carrier G.struct.mul 
              G.struct.mul_assoc G.struct.one G.struct.one_mul G.struct.mul_one 
              G.struct.inv G.struct.mul_left_inv mul_comm)

@[hott, reducible]
def AbGroup_eqv_Group_comm : 
  AbGroup ≃ Σ (G : Group.{u}), Π (a b : G.carrier), a * b = b * a :=
begin
  fapply equiv.mk,
  { intro G, exact dpair (AbGroup.to_Group G) G.struct.mul_comm },
  { fapply adjointify,
    { intro G, exact AbGroup.mk' G.1 G.2 },
    { intro G_comm, hinduction G_comm with G mul_comm, fapply sigma.sigma_eq,
      { hinduction G with G struct_G, hinduction struct_G, exact idp },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intro G, hinduction G with G G_struct, 
      hinduction G_struct with is_set_G mul_G mul_assoc, exact idp } }
end

@[hott, instance]
def AbGroup_to_Group_is_inj : is_injective AbGroup.to_Group :=
begin
  fapply equiv_map_is_injective AbGroup.to_Group sigma.fst AbGroup_eqv_Group_comm,
  { apply eq_of_homotopy, intro CM, exact idp },
  { apply prop_fiber_is_inj, intro G, 
    fapply is_trunc_is_equiv_closed_rev -1 (fiber.fiber_pr1 _ _).to_fun, 
    { apply_instance }, 
    { apply_instance } }
end

@[hott, instance]
def AbGroup_is_cat : is_cat AbGroup := 
  full_subcat_is_cat AbGroup.to_Group

@[hott]
def AbGroup_Category : Category :=
  Category.mk AbGroup.{u} AbGroup_is_cat

@[hott]  --[GEVE]
def unit_AbGroup : AbGroup :=
begin 
  fapply AbGroup.mk', exact unit_Group, 
  intros a b, hinduction a, hinduction b, exact idp 
end

@[hott]  --[GEVE]
def trivial_ab_group_hom (G H : AbGroup) : G ⟶ H :=
begin  
  fapply dpair,
  { fapply group_hom.mk, 
    { intro g, exact H.struct.one },
    { fapply group_hom_str.mk, 
      { intros g₁ g₂, change _ = ab_group.mul _ _, rwr ab_group.mul_one H.struct.one },
      { exact idp } } },
  { exact true.intro }
end

@[hott] 
structure AddAbGroup :=
  (carrier : Type _) 
  (struct' : add_ab_group carrier)

attribute [instance] AddAbGroup.struct'

@[hott] instance has_coe_AddAbGroup : has_coe AddAbGroup (Type _) :=
  ⟨AddAbGroup.carrier⟩

@[hott, reducible]
def AddAbGroup.to_AbGroup : AddAbGroup.{u} -> AbGroup_Category :=
  λ G, AbGroup.mk G.carrier add_ab_group.to_ab_group

@[hott, reducible]
def AddAbGroup_eqv_AbGroup : AddAbGroup ≃ AbGroup :=
begin
  fapply equiv.mk,
  { intro G, exact AddAbGroup.to_AbGroup G },
  { fapply adjointify,
    { intro G, fapply AddAbGroup.mk G.carrier, exact ab_group.to_add_ab_group },
    { intro G, hinduction G, exact idp },
    { intro G, hinduction G, exact idp } }
end  

@[hott, instance]
def AddAbGroup_to_AbGroup_is_inj : is_injective AddAbGroup.to_AbGroup :=
begin
  fapply equiv_map_is_injective AddAbGroup.to_AbGroup id AddAbGroup_eqv_AbGroup,
  { apply eq_of_homotopy, intro G, exact idp },
  { fapply is_injective.mk, intros G₁ G₂, fapply adjointify,
    { exact λ p, p }, 
    { intro p, change G₁ = G₂ at p, hinduction p, exact idp },
    { intro p, hinduction p, exact idp } }
end

@[hott, instance]
def AddAbGroup_is_cat : is_cat AddAbGroup := 
  full_subcat_is_cat AddAbGroup.to_AbGroup

@[hott]
def AddAbGroup_Category : Category :=
  Category.mk AddAbGroup.{u} AddAbGroup_is_cat

@[hott] 
def zero_AddAbGroup : AddAbGroup :=
begin 
  fapply AddAbGroup.mk, exact unit_AbGroup, 
  exact ab_group.to_add_ab_group
end

/- We construct direct products and direct sums of additive abelian groups indexed by sets,
   but do not show their universal properties: Since they are also `ℤ`-modules, we can 
   postpone this to [algebra.ring.submod]. -/
@[hott]
def direct_product_of_AddAbGroups (I : Set) (A : I -> AddAbGroup) : AddAbGroup :=
begin
  fapply AddAbGroup.mk (Π (i : I), (A i).carrier),
  fapply λ s, @ab_group.to_add_ab_group _ s, fapply ab_group.mk,
  { apply_instance },
  { intros a b i, exact a i + b i },
  { intros a b c, apply eq_of_homotopy, intro i, apply (A i).struct'.mul_assoc },
  { intro i, exact (A i).struct'.one },
  { intro a, apply eq_of_homotopy, intro i, apply (A i).struct'.one_mul },
  { intro a, apply eq_of_homotopy, intro i, apply (A i).struct'.mul_one },
  { intros a i, apply @hott.algebra.ab_group.inv _ (A i).struct' (a i) },
  { intro i, apply eq_of_homotopy, intro i, apply (A i).struct'.mul_left_inv },
  { intros a b, apply eq_of_homotopy, intro i, apply (A i).struct'.mul_comm }
end

/- Calculation rules for additive abelian groups. -/
@[hott]
def add_cancel_right {A : Type _} [add_ab_group A] : 
  Π {a b c : A}, a + c = b + c -> a = b :=
begin intros a b c sum_eq, exact add.right_cancel sum_eq end

@[hott]
def neg_add' {A : Type _} [add_ab_group A] : Π {a b : A}, -(a+b) = -a + -b :=
begin  
  intros a b, apply @add_cancel_right _ _ _ _ (a+b), rwr add.assoc, rwr add.comm a b, 
  rwr <- add.assoc (-b) b a, rwr add.left_inv, rwr add.left_inv, rwr zero_add, 
  rwr add.left_inv
end


/- A direct sum of additive abelian groups can be constructed as finite tuples of elements
   in disjoint summands. To avoid questions about the decidability of the index set, we 
   instead follow the same strategy as below for free groups and construct the direct sum as
   a quotient of the set of "additive combinations" (analogous to linear combinations) by an
   equivalence relation. -/
@[hott]
inductive add_comb {J : Set} (A : J -> AddAbGroup)
| zero {} : add_comb
| sum {j : J} (a : (A j).carrier) : add_comb -> add_comb  

/- Additive combinations form a set. -/
@[hott]
def add_comb_code {J : Set} (A : J -> AddAbGroup) : add_comb A -> add_comb A -> Type _ :=
begin
  intro ac₁, hinduction ac₁ with i a ac,
  { intro ac₂, hinduction ac₂ with j b bc, exact One, exact Zero },
  { intro ac₂, hinduction ac₂ with j b bc, exact Zero,
    exact (Σ (p : i = j), a =[p; λ i, (A i).carrier] b) × (ih bc) }
end

@[hott, instance]
def add_comb_code_is_prop {J : Set} (A : J -> AddAbGroup) : 
  Π (ac₁ ac₂ : add_comb A), is_prop (add_comb_code A ac₁ ac₂) :=
begin
  intro ac₁, hinduction ac₁ with i a ac,
  { intro ac₂, hinduction ac₂ with j b bc, by change is_prop One; apply_instance, 
                                           by change is_prop Zero; apply_instance },
  { intro ac₂, hinduction ac₂ with j b bc, by change is_prop Zero; apply_instance, 
    apply @prod.is_trunc_prod _ (add_comb_code A ac bc) -1 _ (ih bc),
    apply @hott.sigma.is_trunc_sigma }
end

@[hott]
def add_comb_refl {J : Set} (A : J -> AddAbGroup) : Π (ac : add_comb A), add_comb_code A ac ac :=
  begin intro ac, hinduction ac with i a ac, exact One.star, exact ⟨⟨idp, idpo⟩, ih⟩ end

@[hott]
def add_comb_decode {J : Set} (A : J -> AddAbGroup) : 
  Π (ac₁ ac₂ : add_comb A), add_comb_code A ac₁ ac₂ -> ac₁ = ac₂ :=
begin
  intros ac₁, hinduction ac₁ with i a₁ ac₁,
  { intro ac₂, hinduction ac₂ with j a₂ ac₂, 
    { intro c, exact idp },
    { intro c, hinduction c } },
  { intro ac₂, hinduction ac₂ with j a₂ ac₂,
    { intro c, hinduction c },
    { intro c, hinduction c.1.1, fapply ap011, apply @eq_of_pathover_idp J (λ j, (A j).carrier),
      have p : c.1.1 = idpath i, from _h, rwr <- p, exact c.1.2, exact ih ac₂ c.2 } }
end

@[hott, instance]
def add_comb_are_set {J : Set} (A : J -> AddAbGroup) : is_set (add_comb A) :=
begin 
  fapply @set.encode_decode_set _ (add_comb_code A) (add_comb_refl A) (add_comb_code_is_prop A), 
  intros a b cd, exact add_comb_decode A _ _ cd 
end

@[hott]
def add_comb.concat {J : Set} (A : J -> AddAbGroup) : 
  add_comb A -> add_comb A -> add_comb A :=
begin 
  intros ac ac', hinduction ac with j a ac,
  { exact ac' },
  { exact add_comb.sum a ih }
end

@[hott, instance]
def add_comb_has_mul {J : Set} (A : J -> AddAbGroup) : has_mul (add_comb A) :=
  has_mul.mk (λ ac₁ ac₂, add_comb.concat A ac₁ ac₂)

@[hott]
def add_comb_Monoid {J : Set.{u}} (A : J -> AddAbGroup.{u}) : Monoid :=
begin  
  fapply Monoid.mk (add_comb A),
  fapply monoid.mk,
  { exact add_comb_are_set A },
  { exact add_comb.concat A },
  { intros ac₁ ac₂ ac₃, hinduction ac₁ with j a ac, exact idp,
    change add_comb.sum a (add_comb.concat A (add_comb.concat A ac ac₂) ac₃) = _, rwr ih },
  { exact add_comb.zero },
  { intro ac, exact idp },
  { intro ac, hinduction ac with j a ac, exact idp,
    change add_comb.sum _ (add_comb.concat A _ _) = _, rwr ih }
end

@[hott, instance]
def add_comb_is_monoid {J : Set.{u}} (A : J -> AddAbGroup.{u}) : monoid (add_comb A) :=
  (add_comb_Monoid A).struct  

@[hott]
def add_comb_sum_add {J : Set.{u}} (A : J -> AddAbGroup.{u}) :
  Π {j : J} (a : (A j).carrier) (ac : add_comb_Monoid A), 
  add_comb.sum a ac = (add_comb.sum a add_comb.zero) * ac :=
begin
  intros j a ac, hinduction ac with j b bc,
  { change _ =  _ * monoid.one (add_comb_Monoid A), exact (monoid.mul_one _)⁻¹ },
  { exact idp }
end

@[hott]
def add_comb_rel {J : Set.{u}} (A : J -> AddAbGroup.{u}) : 
  add_comb_Monoid A -> add_comb_Monoid A -> trunctype.{u} -1
| (@add_comb.sum _ _ i a (@add_comb.sum _ _ j b add_comb.zero)) 
                                 (@add_comb.sum _ _ k c add_comb.zero) := 
  to_Prop (Σ (p : i = k) (q : j = k), (p ▸ a)+(q ▸ b) = c)
| (add_comb.sum a add_comb.zero) add_comb.zero := to_Prop (a = 0)
| (@add_comb.sum _ _ i a (@add_comb.sum _ _ j b add_comb.zero))
                                 (@add_comb.sum _ _ k c (@add_comb.sum _ _ l d add_comb.zero)) :=
  to_Prop (Σ (p : i = l) (q : j = k), (p ▸ a = d) × (q ▸ b = c))
| _ _ := False

@[hott, reducible]
def add_comb_congruence {J : Set.{u}} (A : J -> AddAbGroup.{u}) := 
  rel_to_cong_rel (add_comb_rel A) 

@[hott]
def add_comb_quot_Monoid {J : Set.{u}} (A : J -> AddAbGroup.{u}) : Monoid :=
  (Monoid_cong_quotient (add_comb_congruence A)).carrier

@[hott]
def add_comb_quot_comm_basic {J : Set.{u}} (A : J -> AddAbGroup.{u}) :
  Π {j : J} (a : (A j).carrier) (ac : add_comb_Monoid A), 
  cong_sequence (add_comb_rel A) ((add_comb.sum a add_comb.zero) * ac)  
                                 (ac * (add_comb.sum a add_comb.zero)) :=
begin 
  intros j a ac, hinduction ac with i a₁ ac, 
  { exact cong_sequence.refl _ _ },
  { rwr add_comb_sum_add A a₁, 
    change cong_sequence _ (@monoid.mul (add_comb_Monoid A) _ (add_comb.sum a add_comb.zero) 
                                                                            (monoid.mul _ _)) _,
    rwr <- @monoid.mul_assoc (add_comb_Monoid A) _ _ _ ac, 
    change cong_sequence (add_comb_rel A) ((add_comb.sum a (add_comb.sum a₁ add_comb.zero)) * ac) _,
    apply @cong_sequence.trans (add_comb_Monoid A) _ _ 
                                      ((add_comb.sum a₁ (add_comb.sum a add_comb.zero)) * ac) _,
    { fapply @cong_sequence.mul (add_comb_Monoid A) _ 
                                    (add_comb.sum a (add_comb.sum a₁ add_comb.zero)) _ ac ac,
      { fapply @cong_sequence.rel (add_comb_Monoid A), exact ⟨idp, ⟨idp, ⟨idp, idp⟩⟩⟩ },
      { exact cong_sequence.refl _ ac } },
    { change cong_sequence _ _ (@monoid.mul (add_comb_Monoid A) _ (@monoid.mul (add_comb_Monoid A) _
                                         (add_comb.sum a₁ add_comb.zero) _) _),
      rwr @monoid.mul_assoc (add_comb_Monoid A) _ _ ac, 
      apply @cong_sequence.trans (add_comb_Monoid A) _ _ (monoid.mul (add_comb.sum a₁ 
                           add_comb.zero) (monoid.mul (add_comb.sum a add_comb.zero) ac)),
      { rwr <- @monoid.mul_assoc (add_comb_Monoid A) _ _ _ ac, exact cong_sequence.refl _ _ },
      { fapply @cong_sequence.mul (add_comb_Monoid A) _ (add_comb.sum a₁ add_comb.zero) 
                                                        (add_comb.sum a₁ add_comb.zero) _ _,
        { exact cong_sequence.refl _ _ },
        { exact ih } } } }
end

@[hott]
def add_comb_quot_comm {J : Set.{u}} (A : J -> AddAbGroup.{u}) :
  Π (ac₁ ac₂ : add_comb_quot_Monoid A), ac₁ * ac₂ = ac₂ * ac₁ :=
begin
  fapply set.set_quotient.prec2, intros ac₁ ac₂,
  change set.set_class_of _ _ = set.set_class_of _ _, apply set.eq_of_setrel, apply tr,
  hinduction ac₁ with i a₁ ac₁,
  { change cong_sequence _ _ (monoid.mul _ (monoid.one _)),
    rwr @monoid.mul_one (add_comb_Monoid A) _ ac₂,
    exact cong_sequence.refl _ ac₂ },
  { change ↥(add_comb_Monoid A) at ac₁,  
    change cong_sequence (add_comb_rel A) 
                         (add_comb.sum _ (@monoid.mul (add_comb_Monoid A) _ ac₁ ac₂)) _,
    rwr add_comb_sum_add A, apply @cong_sequence.trans _ _ _ (@monoid.mul (add_comb_Monoid A) _ 
                                          (add_comb.sum a₁ add_comb.zero) (monoid.mul ac₂ ac₁)),
    { fapply @cong_sequence.mul (add_comb_Monoid A) _ (add_comb.sum a₁ add_comb.zero)
               (add_comb.sum a₁ add_comb.zero) _ _ (cong_sequence.refl _ _) ih },
    { rwr <- @monoid.mul_assoc (add_comb_Monoid A) _ _ ac₂ ac₁,
      apply @cong_sequence.trans _ _ _ (@monoid.mul (add_comb_Monoid A) _ 
                                          (monoid.mul ac₂ (add_comb.sum a₁ add_comb.zero)) ac₁),
      { fapply @cong_sequence.mul (add_comb_Monoid A) _ 
                                    (monoid.mul (add_comb.sum a₁ add_comb.zero) ac₂) _ ac₁ ac₁, 
        { exact add_comb_quot_comm_basic A a₁ ac₂ },
        { exact (cong_sequence.refl _ _) } },
      { rwr @monoid.mul_assoc (add_comb_Monoid A) _ ac₂ _ ac₁, 
        rwr add_comb_sum_add A a₁ ac₁, exact (cong_sequence.refl _ _) } } } 
end

@[hott]
def neg_add_comb {J : Set.{u}} (A : J -> AddAbGroup.{u}) : 
  add_comb_Monoid A -> add_comb_Monoid A
| add_comb.zero := add_comb.zero
| (add_comb.sum a ac) := add_comb.sum (-a) (neg_add_comb ac)

@[hott]
def neg_add_comb_quot {J : Set.{u}} (A : J -> AddAbGroup.{u}) : 
  add_comb_quot_Monoid A -> add_comb_quot_Monoid A :=
begin 
  fapply set.set_quotient.rec, 
  { intro ac, exact set.set_class_of _ (neg_add_comb A ac) },
  { intros ac ac' H, hinduction H with H, hinduction H,
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, revert b r,
      fapply @add_comb.rec _ _ (λ a, Π {b : add_comb_Monoid A}, add_comb_rel A a b → 
                cong_sequence (add_comb_rel A) (neg_add_comb A a) (neg_add_comb A b) ), 
      { intros b r, hinduction r },
      { intros i a ac ih, hinduction ac with j a' bc, 
        { intros bc r, hinduction bc with j b bc,
          { have p : a = 0, from r, 
            change cong_sequence (add_comb_rel A) (add_comb.sum (-a) add_comb.zero) add_comb.zero,
            fapply @cong_sequence.rel (add_comb_Monoid A), change -a = 0, rwr p, 
            sorry },
          { sorry } },
        { sorry } } },
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, sorry },
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, sorry },
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, sorry },
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, sorry } }
end

@[hott]
def direct_sum_of_AddAbGroups {J : Set.{u}} (A : J -> AddAbGroup.{u}) : AddAbGroup :=
begin
  fapply is_equiv.inv AddAbGroup_eqv_AbGroup.to_fun, fapply AbGroup.mk',
  { fapply Group.mk,
    { exact (add_comb_quot_Monoid.{u u} A).carrier },
    { fapply group.mk,
      { apply_instance },
      { exact (add_comb_quot_Monoid A).struct.mul },
      { exact (add_comb_quot_Monoid A).struct.mul_assoc },
      { exact (add_comb_quot_Monoid A).struct.one },
      { exact (add_comb_quot_Monoid A).struct.one_mul },
      { exact (add_comb_quot_Monoid A).struct.mul_one },
      { exact neg_add_comb_quot A },
      { sorry } } },
  { exact add_comb_quot_comm A }
end

end algebra

end hott