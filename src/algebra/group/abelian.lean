import algebra.group.quotient algebra.group.subgroup
       
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
def AbGroup_to_Group_functor : AbGroup.{u} ⥤ Group := 
  concrete_forget_functor (AbGroup.to_Group)

@[hott]
def AbGroup_to_Group_functor_is_faithful : is_faithful_functor AbGroup_to_Group_functor :=
  @concrete_forget_functor_is_faithful _ _ (AbGroup.to_Group) _

@[hott]
def AbGroup_Group_map_inv {A B : AbGroup.{u}} (f : A ⟶ B) :
  f.1 = AbGroup_to_Group_functor.map f :=
begin
  fapply sigma.sigma_eq, exact idp, apply pathover_of_tr_eq, exact is_prop.elim _ _
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

@[hott]
def AbGroup.to_AddAbGroup : AbGroup.{u} -> AddAbGroup :=
  λ G, AddAbGroup.mk G.carrier ab_group.to_add_ab_group

@[hott, reducible]
def AddAbGroup_eqv_AbGroup : AddAbGroup ≃ AbGroup :=
begin
  fapply equiv.mk,
  { intro G, exact AddAbGroup.to_AbGroup G },
  { fapply adjointify,
    { intro G, exact AbGroup.to_AddAbGroup G },
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

@[hott]
def AddAbGroup_to_AbGroup_functor : AddAbGroup.{u} ⥤ AbGroup := 
  concrete_forget_functor (AddAbGroup.to_AbGroup)

@[hott]
def AddAbGroup_to_AbGroup_functor_is_faithful : 
  is_faithful_functor AddAbGroup_to_AbGroup_functor :=
  @concrete_forget_functor_is_faithful _ _ (AddAbGroup.to_AbGroup) _

@[hott]
def AbGroup_to_AddAbGroup_functor : AbGroup.{u} ⥤ AddAbGroup :=
begin
  fapply precategories.functor.mk,
  { exact AbGroup.to_AddAbGroup },
  { intros A B f, fapply dpair, exact f, exact true.intro },
  { intro A, exact idp },
  { intros A B C f g, exact idp }
end

@[hott]
def AbGroup_AddAbGroup_map_inv {A B : AddAbGroup.{u}} (f : A ⟶ B) :
  f.1 = AddAbGroup_to_AbGroup_functor.map f :=
begin
  fapply sigma.sigma_eq, exact idp, apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott]
def AddAbGroup_AbGroup_map_inv {A B : AbGroup.{u}} (f : A ⟶ B) :
  f = (AbGroup_to_AddAbGroup_functor.map f).1 :=
idp

@[hott]
def AbGroup_to_AddAbGroup_functor_is_faithful : 
  is_faithful_functor AbGroup_to_AddAbGroup_functor.{u} :=
begin
  intros A B f g hom_eq, exact hom_eq..1
end

@[hott]
def AddAbGroup.to_Group : AddAbGroup.{u} -> Group_Category :=
  λ G, Group.mk G.carrier (@ab_group.to_group G.carrier add_ab_group.to_ab_group)

@[hott]
def AddAbGroup_to_Group_functor : AddAbGroup.{u} ⥤ Group :=
  AddAbGroup_to_AbGroup_functor ⋙ AbGroup_to_Group_functor
  

/- We construct direct products and direct sums of additive abelian groups indexed by sets,
   but do not show their universal properties: Since they are also `ℤ`-modules, we can 
   postpone this to [algebra.ring.submod]. As limits and colimits in the category of additive 
   abelian groups, they must have the same universe level than the indexed groups, so the 
   universe level of the index set cannot be larger than the universe level of the indexed groups. -/
@[hott]
def direct_product_of_AddAbGroups (I : Set.{u'}) (A : I -> AddAbGroup_Category.{max u' u}) : 
  AddAbGroup :=
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

@[hott]
def neg_zero_zero {A : Type _} [add_ab_group A] : -(0:A) = 0 :=
  begin apply @add_cancel_right _ _ _ _ (0:A), rwr add.left_inv, rwr add_zero end

/- A direct sum of additive abelian groups can be constructed as finite tuples of elements
   in disjoint summands. To avoid questions about the decidability of the index set, we 
   instead follow the same strategy as below for free groups and construct the direct sum as
   a quotient of the set of "additive combinations" (analogous to linear combinations) by an
   equivalence relation. -/
@[hott]
inductive add_comb {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u})
| zero {} : add_comb
| sum {j : J} (a : (A j).carrier) : add_comb -> add_comb  

/- Additive combinations form a set. -/
@[hott]
def add_comb_code {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  add_comb A -> add_comb A -> Type (max u u') :=
begin
  intro ac₁, hinduction ac₁ with i a ac,
  { intro ac₂, hinduction ac₂ with j b bc, exact One, exact Zero },
  { intro ac₂, hinduction ac₂ with j b bc, exact Zero,
    exact prod.{(max u u') (max u u')} (Σ (p : i = j), a =[p; λ i, (A i).carrier] b) (ih bc) }
end

@[hott, instance]
def add_comb_code_is_prop {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
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
def add_comb_refl {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  Π (ac : add_comb A), add_comb_code A ac ac :=
begin intro ac, hinduction ac with i a ac, exact One.star, exact ⟨⟨idp, idpo⟩, ih⟩ end

@[hott]
def add_comb_decode {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
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
def add_comb_are_set {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  is_set (add_comb A) :=
begin 
  fapply @set.encode_decode_set _ (add_comb_code A) (add_comb_refl A) (add_comb_code_is_prop A), 
  intros a b cd, exact add_comb_decode A _ _ cd 
end

@[hott]
def add_comb.concat {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  add_comb A -> add_comb A -> add_comb A :=
begin 
  intros ac ac', hinduction ac with j a ac,
  { exact ac' },
  { exact add_comb.sum a ih }
end

@[hott, instance]
def add_comb_has_mul {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : has_mul (add_comb A) :=
  has_mul.mk (λ ac₁ ac₂, add_comb.concat A ac₁ ac₂)

@[hott]
def add_comb_Monoid {J : Set} (A : J -> AddAbGroup_Category) : Monoid :=
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
def add_comb_is_monoid {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  monoid (add_comb A) :=
(add_comb_Monoid A).struct  

@[hott]
def add_comb_sum_add {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) :
  Π {j : J} (a : (A j).carrier) (ac : add_comb_Monoid A), 
  add_comb.sum a ac = (add_comb.sum a add_comb.zero) * ac :=
begin
  intros j a ac, hinduction ac with j b bc,
  { change _ =  _ * monoid.one (add_comb_Monoid A), exact (monoid.mul_one _)⁻¹ },
  { exact idp }
end

@[hott]
def add_comb_rel {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  add_comb_Monoid A -> add_comb_Monoid A -> trunctype.{max u' u} -1
| (@add_comb.sum _ _ i a (@add_comb.sum _ _ j b add_comb.zero)) 
                                 (@add_comb.sum _ _ k c add_comb.zero) := 
  to_Prop (Σ (p : i = k) (q : j = k), (p ▸ a)+(q ▸ b) = c)
| (add_comb.sum a add_comb.zero) add_comb.zero := to_Prop (a = 0)
| (@add_comb.sum _ _ i a (@add_comb.sum _ _ j b add_comb.zero))
                                 (@add_comb.sum _ _ k c (@add_comb.sum _ _ l d add_comb.zero)) :=
  to_Prop (Σ (p : i = l) (q : j = k), (p ▸ a = d) × (q ▸ b = c))
| _ _ := False

@[hott, reducible]
def add_comb_congruence {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) := 
  rel_to_cong_rel (add_comb_rel A) 

@[hott]
def add_comb_quot_Monoid {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : Monoid :=
  (Monoid_cong_quotient (add_comb_congruence A)).carrier

@[hott]
def add_comb_quot_comm_basic {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) :
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
def add_comb_comm_cong_seq {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) :
  Π (ac₁ ac₂ : add_comb_Monoid A), cong_sequence (add_comb_rel A) (ac₁ * ac₂) (ac₂ * ac₁) :=
begin
  intros ac₁ ac₂, hinduction ac₁ with i a₁ ac₁,
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
def add_comb_quot_comm {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) :
  Π (ac₁ ac₂ : add_comb_quot_Monoid A), ac₁ * ac₂ = ac₂ * ac₁ :=
begin
  fapply set.set_quotient.prec2, intros ac₁ ac₂,
  change set.set_class_of _ _ = set.set_class_of _ _, apply set.eq_of_setrel, apply tr,
  exact add_comb_comm_cong_seq A _ _  
end

@[hott]
def neg_add_comb {J : Set.{u'}} (A : J -> AddAbGroup.{max u' u}) : 
  add_comb_Monoid A -> add_comb_Monoid A
| add_comb.zero := add_comb.zero
| (add_comb.sum a ac) := add_comb.sum (-a) (neg_add_comb ac)

@[hott]
def neg_add_comb_add {J : Set.{u'}} {A : J -> AddAbGroup_Category.{max u' u}} : 
  Π (ac₁ ac₂ : add_comb_Monoid A), 
             neg_add_comb A (ac₁ * ac₂) = (neg_add_comb A ac₁) * (neg_add_comb A ac₂) :=
begin
  intros ac₁ ac₂, hinduction ac₁ with i a₁ ac₁, exact idp, 
  change add_comb.sum (-a₁) (neg_add_comb A (ac₁ * ac₂)) = _, rwr ih
end

@[hott]
def neg_add_comb_quot {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  add_comb_quot_Monoid A -> add_comb_quot_Monoid A :=
begin 
  fapply set.set_quotient.rec, 
  { intro ac, exact set.set_class_of _ (neg_add_comb A ac) },
  { intros ac ac' H, hinduction H with H, hinduction H,
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, revert b r,
      fapply @add_comb.rec _ _ (λ a, Π {b : add_comb_Monoid A}, add_comb_rel A a b → 
                cong_sequence (add_comb_rel A) (neg_add_comb A a) (neg_add_comb A b) ), 
      { intros b r, hinduction r },
      { intros i a' ac ih, hinduction ac with j a'' bc, 
        { intros bc' r, hinduction bc' with j b bc',
          { have p : a' = 0, from r, 
            change cong_sequence (add_comb_rel A) (add_comb.sum (-a') add_comb.zero) add_comb.zero,
            fapply @cong_sequence.rel (add_comb_Monoid A), change -a' = 0, rwr p, 
            exact neg_zero_zero },
          { hinduction r } },
        { intros bc' r, hinduction bc' with k b bc', 
          { hinduction bc with l b' bc'', hinduction r, hinduction r },
          { hinduction bc with l b' bc'',
            { hinduction bc' with m b'' bc''',
              { hinduction r with p qs, hinduction qs with q s, hinduction p, hinduction q,
                have s' : a' + a'' = b, from s,
                have neg_s : -a' + -a'' = -b, by rwr <- neg_add'; rwr s', 
                fapply @cong_sequence.rel (add_comb_Monoid A), exact ⟨idp, ⟨idp, neg_s⟩⟩ },
              { hinduction bc''' with n b₃ bc₄, 
                { hinduction r with p₁ pq, hinduction pq with p₂ q, hinduction q with q₁ q₂,
                  hinduction p₁, hinduction p₂, have q₁' : a' = b'', from q₁, 
                  have q₂' : a'' = b, from q₂, fapply @cong_sequence.rel (add_comb_Monoid A),
                  fapply dpair idp, fapply dpair idp, rwr q₁', rwr q₂', exact ⟨idp, idp⟩ },
                { hinduction r } } },
            { hinduction r } } } } },
    { apply pathover_of_eq, apply set.eq_of_setrel, apply tr, exact cong_sequence.refl _ _ },
    { apply pathover_of_eq, apply eq.inverse, exact eq_of_pathover ih },
    { apply pathover_of_eq, exact (eq_of_pathover ih_r) ⬝ (eq_of_pathover ih_r') },
    { apply pathover_of_eq, rwr neg_add_comb_add, rwr neg_add_comb_add, 
      apply λ p, (monoid_hom_laws (Monoid_quotient.is_mon_quot (Monoid_cong_quotient 
                                               (add_comb_congruence A))).proj).mul_comp _ _ ⬝ p,  
      apply λ p, p ⬝ eq.inverse ((monoid_hom_laws (Monoid_quotient.is_mon_quot 
                            (Monoid_cong_quotient (add_comb_congruence A))).proj).mul_comp _ _),
      apply λ p, (ap (λ acl, acl * _) (eq_of_pathover ih_r)) ⬝ p, 
      apply λ p, (ap (λ acl, _ * acl) (eq_of_pathover ih_s)) ⬝ p, exact idp } }
end

@[hott]
def direct_sum_of_AddAbGroups {J : Set.{u'}} (A : J -> AddAbGroup_Category.{max u' u}) : 
  AddAbGroup :=
begin
  fapply is_equiv.inv AddAbGroup_eqv_AbGroup.to_fun, fapply AbGroup.mk',
  { fapply Group.mk,
    { exact (add_comb_quot_Monoid A).carrier },
    { fapply group.mk,
      { apply_instance },
      { exact (add_comb_quot_Monoid A).struct.mul },
      { exact (add_comb_quot_Monoid A).struct.mul_assoc },
      { exact (add_comb_quot_Monoid A).struct.one },
      { exact (add_comb_quot_Monoid A).struct.one_mul },
      { exact (add_comb_quot_Monoid A).struct.mul_one },
      { exact neg_add_comb_quot A },
      { fapply set.set_quotient.prec, intro ac,
        apply λ p, (monoid_hom_laws (Monoid_quotient.is_mon_quot (Monoid_cong_quotient 
                                               (add_comb_congruence A))).proj).mul_comp _ _ ⬝ p,
        apply set.eq_of_setrel, apply tr, hinduction ac with i a ac,
        { exact cong_sequence.refl _ _ },
        { change cong_sequence (add_comb_rel A) 
                   ((add_comb.sum (-a) add_comb.zero * neg_add_comb A ac) * 
                    ((add_comb.sum a add_comb.zero) * ac)) _,
          fapply @cong_sequence.trans (add_comb_Monoid A) _ _ 
                                   (((add_comb.sum (-a) add_comb.zero) * neg_add_comb A ac) * 
                                    (ac * (add_comb.sum a add_comb.zero))),
          { fapply @cong_sequence.mul (add_comb_Monoid A) _ _ _ 
                    ((add_comb.sum a add_comb.zero) * ac) (ac * (add_comb.sum a add_comb.zero)), 
            { exact cong_sequence.refl _ _ },
            { exact add_comb_comm_cong_seq _ _ _ } },
          { change cong_sequence (add_comb_rel A) (@monoid.mul (add_comb_Monoid A) _ 
                       (@monoid.mul (add_comb_Monoid A) _ (add_comb.sum (-a) add_comb.zero) _) 
                       (@monoid.mul (add_comb_Monoid A) _ ac _)) _,
            rwr @monoid.mul_assoc (add_comb_Monoid A) _ _ (neg_add_comb A ac) _,
            rwr <- @monoid.mul_assoc (add_comb_Monoid A) _ (neg_add_comb A ac) _ _,
            fapply @cong_sequence.trans (add_comb_Monoid A) _ _ 
                     ((add_comb.sum (-a) add_comb.zero) * (@monoid.mul (add_comb_Monoid A) _ 
                            (monoid.one (add_comb_Monoid A)) (add_comb.sum a add_comb.zero))),
            { fapply @cong_sequence.mul (add_comb_Monoid A) _ (add_comb.sum (-a) add_comb.zero)
                                                              (add_comb.sum (-a) add_comb.zero),
              { exact cong_sequence.refl _ _ },
              { fapply @cong_sequence.mul (add_comb_Monoid A) _ _ add_comb.zero
                        (add_comb.sum a add_comb.zero) (add_comb.sum a add_comb.zero), 
                { exact ih },
                { exact cong_sequence.refl _ _ } } },
            { rwr @monoid.one_mul (add_comb_Monoid A) _ (add_comb.sum a add_comb.zero),
              fapply @cong_sequence.trans (add_comb_Monoid A) _ _ 
                                              (add_comb.sum (0 : (A i).carrier) add_comb.zero), 
              { fapply @cong_sequence.rel (add_comb_Monoid A), 
                exact ⟨idp, ⟨idp, ab_group.mul_left_inv a⟩⟩ },
              { fapply @cong_sequence.rel (add_comb_Monoid A), exact idp } } } } } } },
  { exact add_comb_quot_comm A }
end

/- Dividing by the commutator subgroup abelianizes a group and satisfies an adjoint property to 
   the forgetful functor from (additive) abelian groups to groups. -/
@[hott]
def commutator {G : Group} : G -> G -> G :=
  λ a b : G, a * b * a⁻¹ * b⁻¹  

def commutator_inv {G : Group} : Π (a b : G), (commutator a b)⁻¹ = commutator b a :=
begin
  intros a b,
  calc (a * b * a⁻¹ * b⁻¹)⁻¹ = (b⁻¹)⁻¹ * (a * b * a⁻¹)⁻¹ : group_mul_inv _ _
       ... = b * _ : by rwr group_inv_inv
       ... = b * ((a⁻¹)⁻¹ * (a * b)⁻¹) : by rwr group_mul_inv
       ... = b * (a * _) : by rwr group_inv_inv
       ... = b * (a * (b⁻¹ * a⁻¹)) : by rwr group_mul_inv
       ... = (b * a) * _ : by rwr (group_laws _).mul_assoc
       ... = b * a * b⁻¹ * a⁻¹ : by rwr <- (group_laws _).mul_assoc
end

@[hott]
def commutator_Subgroup (G : Group.{u}) : Subgroup G :=
  gen_subgroup (λ c, ∥Σ (a b : G), c = commutator a b∥)

@[hott, instance]
def commutator_Subgroup_is_normal {G : Group} : is_normal (commutator_Subgroup G) :=
begin  
  fapply inc_conj_is_normal,
  intro g, apply gen_subgroup_min, intros s s_el, 
  change ↥(s ∈ subset_of_subgroup (Subgroup_of_Subset _ _)), rwr Subgroup_Subset_str,
  apply tr, fapply dpair,
  { exact g⁻¹ * s * g },
  { apply prod.mk,
    { have p : s * (s⁻¹ * g⁻¹ * (s⁻¹)⁻¹ * (g⁻¹)⁻¹) = g⁻¹ * s * g, by 
        rwr group_inv_inv s; rwr group_inv_inv g;
        rwr <- (group_laws _).mul_assoc s; rwr <- (group_laws _).mul_assoc s;
        rwr <- (group_laws _).mul_assoc s; rwr Group_left_inv_is_right_inv; 
        rwr (group_laws _).one_mul, 
      have s_el' : ↥(s∈subset_of_subgroup (commutator_Subgroup G)), from 
        gen_inc_gen_subgroup _ s s_el,
      have comm_el : ↥(s⁻¹ * g⁻¹ * (s⁻¹)⁻¹ * (g⁻¹)⁻¹∈subset_of_subgroup (commutator_Subgroup G)), from 
        begin apply gen_inc_gen_subgroup, apply tr, exact ⟨s⁻¹, ⟨g⁻¹, idp⟩⟩ end,
      rwr <- p, exact (subgroup_laws _).mul s_el' comm_el },
    { rwr <- (group_laws _).mul_assoc g, rwr <- (group_laws _).mul_assoc g, 
      rwr Group_left_inv_is_right_inv, rwr (group_laws _).one_mul, 
      rwr (group_laws _).mul_assoc, rwr Group_left_inv_is_right_inv, rwr (group_laws _).mul_one } }
end

@[hott]
def abelianized_Group (G : Group.{u}) : AbGroup :=
begin
  fapply AbGroup.mk',
  { exact @quotient_Group_by_normal_subgroup G (commutator_Subgroup G) 
                                                  (@commutator_Subgroup_is_normal G)},
  { fapply set.set_quotient.prec2, change Π (a b : Group_to_Set_functor.obj G), _, intros a b, 
    change set.set_class_of _ _ = set.set_class_of _ _, apply set.eq_of_setrel, 
    change ↥((a * b)⁻¹ * (b * a) ∈ subset_of_subgroup _), apply gen_inc_gen_subgroup,
    apply tr, apply dpair b⁻¹, apply dpair a⁻¹, apply eq.inverse,
    calc b⁻¹ * a⁻¹ * (b⁻¹)⁻¹ * (a⁻¹)⁻¹ = b⁻¹ * a⁻¹ * b * a : by rwr group_inv_inv; rwr group_inv_inv
         ... = b⁻¹ * a⁻¹ * (b * a) : (group_laws _).mul_assoc _ b _
         ... = (a * b)⁻¹ * (b * a) : by rwr (group_mul_inv _ _) }
end

@[hott, reducible]
def abelianized_Group_proj (G : Group) : 
  G ⟶ (AbGroup.to_Group (abelianized_Group G)) :=
(quot_Group_is_group_quot (commutator_Subgroup G)).proj

@[hott]
def abelianize_adjoint_hom_inc {G : Group} {A : AbGroup} (f : G ⟶ AbGroup.to_Group A) :
  commutator_Subgroup G ≼ kernel_subgroup f :=
begin 
  apply gen_subgroup_min, intros g g_el, hinduction g_el with g_comm,
  hinduction g_comm with a g_comm', hinduction g_comm' with b comm_eq,
  change ↥(g ∈ subset_of_subgroup (Subgroup_of_Subset _ _)), rwr Subgroup_Subset_str, 
  change Group_to_Set_functor.map f g = 1, rwr comm_eq, 
  change Group_to_Set_functor.map f (a * b * a⁻¹ * b⁻¹) = 1,
  rwr (group_hom_laws _).mul_comp, rwr (group_hom_laws _).mul_comp, 
  rwr (group_hom_laws _).mul_comp, rwr (group_laws _).mul_assoc (Group_to_Set_functor.map f a), 
  change _ * (ab_group.mul _ _) * _ = (1:A), rwr ab_group.mul_comm, 
  change _ * (_ * _) * _ = (1:A), rwr <- (group_laws _).mul_assoc (Group_to_Set_functor.map f a),
  rwr <- (group_hom_laws _).mul_comp, rwr Group_left_inv_is_right_inv, 
  rwr <- (group_hom_laws _).mul_comp, rwr (group_laws _).one_mul,
  rwr <- (group_hom_laws _).mul_comp, rwr Group_left_inv_is_right_inv, 
  exact (group_hom_laws _).one_comp 
end

@[hott]
def abelianize_adjoint_hom_exists {G : Group} {A : AbGroup} (f : G ⟶ AbGroup.to_Group A) : 
  Σ (g : abelianized_Group G ⟶ A),
      f = abelianized_Group_proj G ≫ (AbGroup_to_Group_functor).map g :=
begin
   fapply dpair,
   { fapply dpair,   
     { exact ((group_quotient_is_univ _ _ (quot_Group_is_group_quot _)).factors f 
              (abelianize_adjoint_hom_inc f)).1 },
     { exact true.intro} },
   { exact ((group_quotient_is_univ _ _ (quot_Group_is_group_quot _)).factors f 
              (abelianize_adjoint_hom_inc f)).2 } 
end

@[hott]
def abelianize_adjoint_hom_unique {G : Group.{u}} {A : AbGroup} (g h : abelianized_Group G ⟶ A) : 
      abelianized_Group_proj G ≫ (AbGroup_to_Group_functor).map g = 
         abelianized_Group_proj G ≫ (AbGroup_to_Group_functor).map h -> g = h :=
begin
  intro proj_eq, apply AbGroup_to_Group_functor_is_faithful, 
  exact is_univ_group_quotient.unique (group_quotient_is_univ _ _ (quot_Group_is_group_quot 
          (commutator_Subgroup G))) _ _ _ proj_eq
end

set_option profiler true

/- Subobjects of (additive) abelian groups `A` are just subgroups of the group `A`. -/
@[hott]
def subobj_AddAbGroup_to_AbGroup (A : AddAbGroup_Category.{u}) : 
  (set.to_Set (subobject A)) -> (set.to_Set (subobject (AddAbGroup.to_AbGroup A))) :=
begin
  intro B, fapply subobject.mk,
  { exact AddAbGroup.to_AbGroup B.obj },
  { exact AddAbGroup_to_AbGroup_functor.map B.hom }, 
  { intros C f g hom_eq, apply AbGroup_to_AddAbGroup_functor_is_faithful, 
    apply B.is_mono, apply AddAbGroup_to_AbGroup_functor_is_faithful, 
    apply λ p, functor.map_comp _ _ _ ⬝ p ⬝ eq.inverse (functor.map_comp _ _ _),
    apply λ p, (ap (λ f, f ≫ _) (AbGroup_AddAbGroup_map_inv _)) ⬝ p ⬝ 
                 (ap (λ f, f ≫ _) (eq.inverse (AbGroup_AddAbGroup_map_inv _))),
    exact hom_eq }
end

@[hott]
def subobj_AbGroup_to_AddAbGroup (A : AddAbGroup_Category.{u}) : 
  (set.to_Set (subobject (AddAbGroup.to_AbGroup A))) -> (set.to_Set (subobject A)) :=
begin
  intro B, fapply subobject.mk,
  { exact AbGroup.to_AddAbGroup B.obj },
  { fapply dpair, exact B.hom, exact true.intro },
  { intros C f g hom_eq, apply AddAbGroup_to_AbGroup_functor_is_faithful,
    apply B.is_mono, 
    let hom_eq' := ap (precategories.functor.map AddAbGroup_to_AbGroup_functor) hom_eq,
    let hom_eq'' := eq.inverse (functor.map_comp _ _ _) ⬝ hom_eq' ⬝ 
                                 (functor.map_comp _ _ _),
    let hom_eq''' := (ap (λ h, AddAbGroup_to_AbGroup_functor.map f ≫ h) 
                                          (AbGroup_AddAbGroup_map_inv _)) ⬝ hom_eq'' ⬝
            (ap (λ h, AddAbGroup_to_AbGroup_functor.map g ≫ h) 
                                         (eq.inverse (AbGroup_AddAbGroup_map_inv _))),
    exact hom_eq''' }
end

@[hott]
def subobj_of_AddAbGroup_AbGroup (A : AddAbGroup_Category.{u}) : 
  set.bijection (set.to_Set (subobject A)) 
                (set.to_Set (subobject (AddAbGroup.to_AbGroup A))) :=
begin
  fapply set.has_inverse_to_bijection,
  { exact subobj_AddAbGroup_to_AbGroup A },
  { exact subobj_AbGroup_to_AddAbGroup A },
  { fapply set.is_set_inverse_of.mk,
    { intro B, fapply subobj_antisymm, 
      { fapply hom_of_monos.mk,
        { exact 𝟙 B.obj },
        { exact is_precat.id_comp B.hom } },
      { fapply hom_of_monos.mk,
        { exact 𝟙 B.obj },
        { exact is_precat.id_comp B.hom } } },
    { intro B, fapply subobj_antisymm, 
      { fapply hom_of_monos.mk,
        { exact 𝟙 B.obj },
        { apply λ p, is_precat.id_comp B.hom ⬝ p, fapply sigma.sigma_eq,
          { exact idp },
          { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } },
      { fapply hom_of_monos.mk,
        { exact 𝟙 B.obj },
        { exact is_precat.id_comp B.hom } } } }
end

@[hott]
def subobj_AbGroup_to_Group (A : AbGroup_Category) : 
  (set.to_Set (subobject A)) -> (set.to_Set (Subgroup (AbGroup.to_Group A))) :=
begin
  intro B, fapply subobject.mk,
  { exact AbGroup.to_Group B.obj },
  { exact AbGroup_to_Group_functor.map B.hom },
  { intros C f g hom_eq, 
    let pf := (abelianize_adjoint_hom_exists f).2, rwr pf at hom_eq, rwr pf,
    let pg := (abelianize_adjoint_hom_exists g).2, rwr pg at hom_eq, rwr pg, 
    apply λ p, ap (λ h, abelianized_Group_proj C ≫ (AbGroup_to_Group_functor.map h)) p, 
    apply B.is_mono, apply abelianize_adjoint_hom_unique,
    apply λ p, ap (λ h, abelianized_Group_proj C ≫ h) 
                               (functor.map_comp AbGroup_to_Group_functor _ _) ⬝ p ⬝
               eq.inverse (ap (λ h, abelianized_Group_proj C ≫ h) 
                                 (functor.map_comp AbGroup_to_Group_functor _ _)),
    apply λ p, eq.inverse (is_precat.assoc _ _ _) ⬝ p ⬝ is_precat.assoc _ _ _,
    rwr hom_eq }
end

@[hott]
def subobj_Group_to_AbGroup (A : AbGroup_Category) : 
  (set.to_Set (Subgroup (AbGroup.to_Group A))) -> (set.to_Set (subobject A)) :=
begin
  intro B, fapply subobject.mk,
  { fapply AbGroup_eqv_Group_comm.to_is_equiv.inv, fapply dpair,
    { exact B.obj },
    { intros a b, apply (group_mon_is_inj B.hom).1 B.is_mono, 
      rwr (group_hom_laws _).mul_comp, rwr (group_hom_laws _).mul_comp, 
      exact ab_group.mul_comm _ _ } },
  { exact dpair B.hom true.intro },
  { intros C f g hom_eq, apply AbGroup_to_Group_functor_is_faithful, apply B.is_mono,
    --let hom_eq' := ap (precategories.functor.map AbGroup_to_Group_functor) hom_eq,
    --let hom_eq'' := eq.inverse (functor.map_comp _ _ _) ⬝ hom_eq' ⬝ 
      --                           (functor.map_comp _ _ _),
    apply λ p, eq.inverse (ap (λ h, AbGroup_to_Group_functor.map f ≫ h) 
                                               (AbGroup_Group_map_inv ⟨B.hom, true.intro⟩)) ⬝ p ⬝
                     ap (λ h, AbGroup_to_Group_functor.map g ≫ h) 
                                               (AbGroup_Group_map_inv _),
    sorry }--exact hom_eq''' }
end

@[hott]
def subobj_of_AbGroup_Group (A : AbGroup_Category) : 
  set.bijection (set.to_Set (subobject A)) (set.to_Set (Subgroup (AbGroup.to_Group A))) :=
begin
  fapply set.has_inverse_to_bijection,
  { exact subobj_AbGroup_to_Group A },
  { exact subobj_Group_to_AbGroup A },
  { fapply set.is_set_inverse_of.mk,
    { sorry },
    { sorry } }
end

@[hott]
def subobj_of_AddAbGroup_Group (A : AddAbGroup_Category) : 
  set.bijection (set.to_Set (subobject A)) (set.to_Set (Subgroup (AddAbGroup.to_Group A))) :=
set.comp_bijection (subobj_of_AddAbGroup_AbGroup A) (subobj_of_AbGroup_Group _)

end algebra

end hott