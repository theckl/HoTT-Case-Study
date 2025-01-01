import algebra.monoid.quotient 
       

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.is_equiv subset precategories categories categories.sets

namespace algebra

/- For later calculations, the group laws should be available with `1`, `*` and `⁻¹` - 
   the `rwr`-tactic does not accept these notations from the group structure directly. -/
@[hott]
structure group_str (G : Group) :=
  (mul_assoc : Π (g₁ g₂ g₃ : G), (g₁ * g₂) * g₃ = g₁ * (g₂ * g₃))
  (mul_one : Π g : G, g * 1 = g)
  (one_mul : Π g : G, 1 * g = g)
  (mul_left_inv : Π g : G, g⁻¹ * g = 1)

@[hott]
def group_laws (G : Group) : group_str G :=
  group_str.mk group.mul_assoc group.mul_one group.one_mul group.mul_left_inv 

/- Groups form a subcategory of the category of monoids. -/
@[hott, reducible]
def Group.to_Monoid : Group.{u} -> Monoid_Category :=
  λ G, Monoid.mk G.carrier (monoid.mk G.struct.is_set_carrier G.struct.mul 
                     G.struct.mul_assoc G.struct.one G.struct.one_mul G.struct.mul_one)

@[hott, reducible]
def Group_eqv_Monoid_inv_law : 
  Group ≃ Σ (M : Monoid.{u}) (inv : M -> M), Π (a : M), (inv a * a) = 1 :=
begin
  fapply equiv.mk,
  { intro G, exact dpair (Group.to_Monoid G) 
                         (dpair G.struct.inv G.struct.mul_left_inv) },
  { fapply adjointify,
    { intro M, exact Group.mk M.1.carrier (group.mk M.1.struct.is_set_carrier 
        M.1.struct.mul M.1.struct.mul_assoc M.1.struct.one M.1.struct.one_mul 
        M.1.struct.mul_one M.2.1 M.2.2) },
    { intro M_inv_law, hinduction M_inv_law with M inv_law, 
      hinduction M with M M_mon, hinduction M_mon, hinduction inv_law, exact idp },
    { intro G, hinduction G with G G_struct, hinduction G_struct, exact idp } }
end

@[hott]
def Monoid_left_inv_is_right_inv {M : Monoid.{u}} (inv : M -> M) 
  (law : Π (a : M), (inv a * a) = 1) : Π (a : M), a * inv a = 1 :=
begin
  intro a,
  calc a * inv a = 1 * (a * inv a) : (monoid.one_mul (a * inv a))⁻¹
       ... = inv (a * inv a) * (a * inv a) * (a * inv a) : by rwr <- law (a * inv a)
       ... = inv (a * inv a) * ((a * inv a) * (a * inv a)) : monoid.mul_assoc _ _ _
       ... = inv (a * inv a) * (a * (inv a * (a * inv a))) : 
                  ap (λ c, inv (a * inv a) * c) (monoid.mul_assoc a (inv a) (a * inv a))
       ... = inv (a * inv a) * (a * ((inv a * a) * inv a)) : 
               ap (λ c, inv (a * inv a) * (a * c)) (monoid.mul_assoc (inv a) a (inv a))⁻¹
       ... = inv (a * inv a) * (a * (1 * inv a)) : by rwr law a 
       ... = inv (a * inv a) * (a * inv a) : 
                      ap  (λ c, inv (a * inv a) * (a * c)) (monoid.one_mul (inv a))
       ... = 1 : law (a * inv a)
end

@[hott]
def Group_left_inv_is_right_inv {G : Group} : Π (g : G), g * g⁻¹ = 1 :=
   @Monoid_left_inv_is_right_inv (Group.to_Monoid G) G.struct.inv G.struct.mul_left_inv

@[hott,instance]
def Monoid_inverse_is_unique (M : Monoid.{u}) : 
  is_prop (Σ (inv : M -> M), Π (a : M), (inv a * a) = 1) :=
begin
  fapply is_prop.mk, intros inv_law₁ inv_law₂, 
  hinduction inv_law₁ with inv₁ law₁, hinduction inv_law₂ with inv₂ law₂,
  have p : inv₁ = inv₂, from 
  begin 
    apply eq_of_homotopy, intro a, 
    calc inv₁ a = inv₁ a * 1 : (monoid.mul_one _)⁻¹
         ... = inv₁ a * (a * inv₂ a) : by rwr <- Monoid_left_inv_is_right_inv inv₂ law₂ a
         ... = (inv₁ a * a) * inv₂ a : (monoid.mul_assoc _ _ _)⁻¹
         ... = 1 * inv₂ a : by rwr law₁ a
         ... = inv₂ a : monoid.one_mul _ 
  end,
  hinduction p, fapply sigma.sigma_eq,
  { exact idp },
  { apply pathover_idp_of_eq, exact is_prop.elim _ _ }
end

@[hott]
def Group_inverse_is_unique {G : Group} : Π (g h : G), g * h = 1 -> g = h⁻¹ :=
begin
  intros g h inv_eq, 
  calc g = g * 1 : (group.mul_one g)⁻¹
       ... = g * (h * h⁻¹) : by rwr <- Group_left_inv_is_right_inv h 
       ... = (g * h) * h⁻¹ : (group.mul_assoc _ _ _)⁻¹
       ... = 1 * h⁻¹ : by rwr inv_eq
       ... = h⁻¹ : group.one_mul _
end

@[hott]
def group_one_inv_one (G : Group) : (1 : G) = 1⁻¹ :=
  begin apply Group_inverse_is_unique, exact group.mul_one 1 end

@[hott]
def group_mul_inv {G : Group} : Π (g h : G), (g * h)⁻¹ = h⁻¹ * g⁻¹ :=
begin
  intros g h, apply eq.inverse, apply Group_inverse_is_unique,
  rwr (group_laws G).mul_assoc, rwr <- (group_laws G).mul_assoc _ g h, 
  rwr (group_laws G).mul_left_inv g, rwr (group_laws G).one_mul, 
  rwr (group_laws G).mul_left_inv
end

@[hott]
def group_inv_inv {G : Group} : Π (g : G), (g⁻¹)⁻¹ = g :=
begin 
  intro g, apply eq.inverse, apply Group_inverse_is_unique, 
  exact Group_left_inv_is_right_inv g
end 

@[hott, instance]
def Group_to_Monoid_is_inj : is_injective Group.to_Monoid :=
begin
  fapply equiv_map_is_injective Group.to_Monoid sigma.fst Group_eqv_Monoid_inv_law,
  { apply eq_of_homotopy, intro G, exact idp },
  { apply prop_fiber_is_inj, intro M, 
    fapply is_trunc_is_equiv_closed_rev -1 (fiber.fiber_pr1 _ _).to_fun, 
    { apply_instance }, 
    { apply_instance } }
end

@[hott, instance]
def Group_is_cat : is_cat Group := 
  full_subcat_is_cat Group.to_Monoid

@[hott]
def Group_Category : Category :=
  Category.mk Group.{u} Group_is_cat

@[hott]  --[GEVE]
def unit_Group : Group :=
begin
  fapply Group.mk, exact One,
  fapply group.mk, 
  { apply_instance }, 
  { exact λ o₁ o₂, One.star }, 
  { exact λ o₁ o₂ o₃, idp }, 
  { exact One.star }, 
  { intro a, hinduction a, exact idp },
  { intro a, hinduction a, exact idp },
  { exact id },
  { exact λ o, idp }
end  

/- For calculations with group homomorphisms, it is more effective to extract the laws
   of a homomorphism. -/
@[hott]
def group_of_monoid_hom {G H : Group} : (Group.to_Monoid G ⟶ Group.to_Monoid H) ->
  (G ⟶ H) :=
λ f, dpair f true.intro

@[hott, reducible]
def Group_to_Set_functor : Group ⥤ Set :=
  concrete_forget_functor (Group.to_Monoid) ⋙ Monoid_to_Set_functor

@[hott]
def Group_to_Monoid_to_Set_functor {G H : Group} : 
  Π (f : Group.to_Monoid G ⟶ Group.to_Monoid H) (g : Group_to_Set_functor.obj G), 
     Group_to_Set_functor.map (group_of_monoid_hom f) g = Monoid_to_Set_functor.map f g :=
λ f g, idp

@[hott, instance]
def Group_Set_has_mul (G : Group) : has_mul (Group_to_Set_functor.obj G) :=
begin apply has_mul.mk, change G -> G -> G, intros g₁ g₂, exact g₁ * g₂ end

@[hott, instance]
def Group_Set_has_one (G : Group) : has_one (Group_to_Set_functor.obj G) :=
begin apply has_one.mk, change G.carrier, exact G.struct.one end

@[hott, instance]
def Group_Set_has_inv (G : Group) : has_inv (Group_to_Set_functor.obj G) :=
begin apply has_inv.mk, change G.carrier -> G.carrier, exact G.struct.inv end

@[hott]
structure group_hom_str {G H : Group} (f : G.carrier -> H.carrier) :=
  (mul_comp : Π (g₁ g₂ : G), f (g₁ * g₂) = f g₁ * f g₂)
  (one_comp : f 1 = 1) 

@[hott]
def group_hom_laws {G H : Group} (f : G ⟶ H) : 
  group_hom_str (Group_to_Set_functor.map f) :=
begin
  hinduction f with f, hinduction f with f one, hinduction f with f,
  hinduction f with f mul, exact group_hom_str.mk mul one 
end  

@[hott]
def group_hom_inv {G H : Group} (f : G ⟶ H) : 
  Π (g : G), Group_to_Set_functor.map f g⁻¹ = (Group_to_Set_functor.map f g)⁻¹ := 
begin
  let f' : G -> H := Group_to_Set_functor.map f,
  intro g, change f' g⁻¹ = (f' g)⁻¹,
  calc f' g⁻¹ = 1 * f' g⁻¹ : (group.one_mul _)⁻¹
       ... = (f' g)⁻¹ * f' g * f' g⁻¹ : ap (λ c, c * f' g⁻¹) (group.mul_left_inv (f' g))⁻¹
       ... = (f' g)⁻¹ * (f' g * f' g⁻¹) : group.mul_assoc _ _ _ 
       ... = (f' g)⁻¹ * f' (g * g⁻¹) : by rwr <- (group_hom_laws f).mul_comp
       ... = (f' g)⁻¹ * f' 1 : by rwr <- Group_left_inv_is_right_inv g
       ... = (f' g)⁻¹ * 1 : ap (λ c, (f' g)⁻¹ * c) (group_hom_laws f).one_comp 
       ... = (f' g)⁻¹ : group.mul_one _
end

@[hott]  --[GEVE]
def group_hom.mk {G H : Group} (f : G -> H) : 
  group_hom_str f -> (G ⟶ H) :=
λ group_hom_str, 
          ⟨⟨⟨⟨f, group_hom_str.mul_comp⟩, true.intro⟩, group_hom_str.one_comp⟩, true.intro⟩

@[hott]  --[GEVE]
def trivial_group_hom (G H : Group) : G ⟶ H :=
begin  
  apply group_hom.mk (λ g, H.struct.one), fapply group_hom_str.mk, 
  { intros g₁ g₂, change _ = group.mul _ _, rwr group.mul_one H.struct.one },
  { exact idp }
end

@[hott]
def init_group_hom (G : Group) : unit_Group ⟶ G :=
begin
  fapply group_hom.mk (λ s, G.struct.one), fapply group_hom_str.mk,
  { intros m₁ m₂, change _ = group.mul _ _, rwr group.mul_one G.struct.one },
  { exact idp }
end

@[hott]  --[GEVE]
def Group_to_Set_functor_is_faithful : is_faithful_functor (Group_to_Set_functor) :=
begin 
  fapply faithful_is_trans (concrete_forget_functor (Group.to_Monoid)), 
  { apply @concrete_forget_functor_is_faithful _ _ Group.to_Monoid },
  { apply Monoid_to_Set_functor_is_faithful }  
end  

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

/- We characterize free groups by their universal property. Then we construct
   a free group as the quotient of the type of lists over the set of generators and 
   their inverses, dividing out the inverseness equalities. -/
@[hott]
structure is_ind_free_group_of (A : Set.{u}) (F : Group.{u}) :=
  (h : A -> F)
  (map : Π {H : Group} (f : A -> H), Σ (g : F ⟶ H), Π (a : A), f a = 
                                                       Group_to_Set_functor.map g (h a))
  (unique : Π {H : Group} (g₁ g₂ : F ⟶ H), (Π (a : A),
      Group_to_Set_functor.map g₁ (h a) = Group_to_Set_functor.map g₂ (h a)) -> g₁ = g₂)

@[hott, reducible]
def word_Monoid (A : Set.{u}) : Monoid.{u} := List_Monoid (set.to_Set (A ⊎ A))

@[hott]
def inv_letter_word {A : Set.{u}} : word_Monoid A -> word_Monoid A 
| []              := []
| (sum.inl a::tl) := sum.inr a::(inv_letter_word tl)
| (sum.inr a::tl) := sum.inl a::(inv_letter_word tl)

@[hott]
def rev_word {A : Set.{u}} : word_Monoid A -> word_Monoid A :=
  λ w, list.reverse w

@[hott, reducible]
def inv_word {A : Set.{u}} : word_Monoid A -> word_Monoid A :=
  λ w, rev_word (inv_letter_word w) 

@[hott]
def inv_letter_mul_word {A : Set.{u}} : Π (a b : word_Monoid A),
  inv_letter_word (a * b) = inv_letter_word a * inv_letter_word b :=
begin 
  intros a b, hinduction a, exact idp, change inv_letter_word (_::_) = _, 
  hinduction hd, change _ :: inv_letter_word (tl * b) = _, rwr ih,
                 change _ :: inv_letter_word (tl * b) = _, rwr ih 
end

@[hott]
def rev_mul_cons_word {A : Set.{u}} : Π (a : A ⊎ A) (b : word_Monoid A),
  rev_word (a :: b) = monoid.mul (rev_word b) [a] :=
begin
  intros a b, change list.reverse_core _ [a] = list.append (list.reverse _) _, 
  exact list_reverse_append _ _
end

@[hott]
def rev_mul_word {A : Set.{u}} : Π (a b : word_Monoid A),
  rev_word (a * b) = list.reverse b * list.reverse a :=
begin 
  intros a b, hinduction a, exact (monoid.mul_one _)⁻¹,
  change rev_word (hd :: _) = _, rwr rev_mul_cons_word, 
  change rev_word (list.append _ _) = _ at ih, rwr ih,
  change monoid.mul (monoid.mul _ (rev_word _)) _ = _,
  rwr monoid.mul_assoc _ (rev_word _) _, rwr <- rev_mul_cons_word 
end

@[hott]
def inv_mul_word {A : Set.{u}} : Π (a b : word_Monoid A), 
  inv_word (a * b) = inv_word b * inv_word a :=
begin intros a b, change rev_word _ = _, rwr inv_letter_mul_word, rwr rev_mul_word end 

@[hott]
def word_cancel_rel (A : Set.{u}) : 
  Monoid_to_Set_functor.obj (word_Monoid.{u u} A) -> 
  Monoid_to_Set_functor.obj (word_Monoid.{u u} A) -> trunctype.{u} -1
| (sum.inl a::[sum.inr b]) [] := to_Prop (a = b)
| (sum.inr a::[sum.inl b]) [] := to_Prop (a = b)
| _                        _  := False

@[hott]
def word_cancel_rel.rec {A : Set.{u}} 
  {P : Π (a b : Monoid_to_Set_functor.obj (word_Monoid A)), Type _} 
  (rec_l : Π (a b : A), (word_cancel_rel A (sum.inl a::[sum.inr b]) []) -> 
                                                          P (sum.inl a::[sum.inr b]) []) 
  (rec_r : Π (a b : A), (word_cancel_rel A (sum.inr a::[sum.inl b]) []) -> 
                                                          P (sum.inr a::[sum.inl b]) []) : 
  Π {a b : Monoid_to_Set_functor.obj (word_Monoid A)}, (word_cancel_rel A a b) -> P a b :=
begin 
  intros a b, exact match a, b with
  | (sum.inl a::[sum.inr b]), [] := λ r, rec_l a b r 
  | (sum.inr a::[sum.inl b]), [] := λ r, rec_r  a b r 
  | [], _ := by intro r; hinduction r
  | [sum.inl a], _  := by intro r; hinduction r
  | [sum.inr a], _  := by intro r; hinduction r
  | sum.inl a::sum.inl b::c, _  := by intro r; hinduction r
  | sum.inl a::[sum.inr b], c::d := by intro r; hinduction r
  | sum.inr a::sum.inr b::c, _  := by intro r; hinduction r
  | sum.inr a::[sum.inl b], c::d := by intro r; hinduction r
  | sum.inl a::sum.inr b::c::d, _ := by intro r; hinduction r
  | sum.inr a::sum.inl b::c::d, _ := by intro r; hinduction r
  end
end

@[hott, reducible]
def word_congruence (A : Set.{u}) := rel_to_cong_rel (word_cancel_rel A) 

@[hott]
def word_quot_Monoid (A : Set.{u}) : Monoid.{u} :=
  (Monoid_cong_quotient.{u} (rel_to_cong_rel (word_cancel_rel A))).carrier

@[hott]
def word_quot_Monoid_inv {A : Set.{u}} : 
  word_quot_Monoid A -> word_quot_Monoid A :=
begin
  fapply set.set_quotient.rec, 
  { exact λ w, set.set_class_of (word_congruence A) (inv_word w) },
  { intros w₁ w₂ H, apply pathover_of_eq, 
    apply set.eq_of_setrel, hinduction H with H, hinduction H,
    { revert r, fapply word_cancel_rel.rec, 
      { intros a b r, apply tr, apply cong_sequence.rel, change b = a, exact r⁻¹ },
      { intros a b r, apply tr, apply cong_sequence.rel, change b = a, exact r⁻¹ } },
    { exact relation.rel_refl (λ b c, word_congruence A b c) _ },
    { exact relation.rel_symm (λ b c, word_congruence A b c) ih },
    { exact relation.rel_trans (λ b c, word_congruence A b c) ih_r ih_r' },
    { rwr inv_mul_word, rwr inv_mul_word, hinduction ih_r, hinduction ih_s,
      apply tr, exact cong_sequence.mul a_2 a_1 } }
end 

@[hott]
def word_quot_Monoid_inv_law (A : Set.{u}) : 
  Π (a : word_quot_Monoid A), (word_quot_Monoid_inv a * a) = 1 :=
begin  
  fapply set.set_quotient.prec, intro w,
  change set.set_class_of _ _ = 1, apply set.eq_of_setrel, apply tr,
  hinduction w, 
  { exact cong_sequence.refl _ [] },
  { hinduction hd with a a,
    { have p : inv_word (sum.inl a :: tl) * (sum.inl a :: tl) = 
                                      inv_word tl * [sum.inr a, sum.inl a] * tl, from 
      begin 
        change inv_word ([sum.inl a] * tl) * ([sum.inl a] * tl) = _,
        rwr inv_mul_word, 
        change monoid.mul (monoid.mul _ [sum.inr a]) (monoid.mul _ _) = _,
        rwr monoid.mul_assoc, rwr <- monoid.mul_assoc [sum.inr a],
        rwr <- monoid.mul_assoc
      end,
      rwr p, apply cong_sequence.trans _ ih, fapply cong_sequence.mul,
      { rwr <- monoid.mul_one (inv_word tl),
        fapply cong_sequence.mul,
        { rwr monoid.mul_one, exact cong_sequence.refl _ _ },
        { apply cong_sequence.rel, exact idp } },
      { exact cong_sequence.refl _ _ } },
    { have p : inv_word (sum.inr a :: tl) * (sum.inr a :: tl) = 
               inv_word tl * [sum.inl a, sum.inr a] * tl, from 
      begin 
        change inv_word ([sum.inr a] * tl) * ([sum.inr a] * tl) = _,
        rwr inv_mul_word, 
        change monoid.mul (monoid.mul _ [sum.inl a]) (monoid.mul _ _) = _,
        rwr monoid.mul_assoc, rwr <- monoid.mul_assoc [sum.inl a],
        rwr <- monoid.mul_assoc
      end,
      rwr p, apply cong_sequence.trans _ ih, fapply cong_sequence.mul,
      { rwr <- monoid.mul_one (inv_word tl),
        fapply cong_sequence.mul,
        { rwr monoid.mul_one, exact cong_sequence.refl _ _ },
        { apply cong_sequence.rel, exact idp } },
      { exact cong_sequence.refl _ _ } } }  
end 

@[hott]
def word_quot_Group (A : Set.{u}) : Group.{u} := 
begin
  fapply Group.mk,
  { exact (word_quot_Monoid A).carrier },
  { fapply group.mk, apply_instance, exact (word_quot_Monoid A).struct.mul,
    exact (word_quot_Monoid A).struct.mul_assoc, exact (word_quot_Monoid A).struct.one,
    exact (word_quot_Monoid A).struct.one_mul, exact (word_quot_Monoid A).struct.mul_one,
    exact @word_quot_Monoid_inv A, exact word_quot_Monoid_inv_law A }
end

@[hott]
def group_gen_to_monoid_gen_map {A : Set.{u}} {H : Group.{u}} (f : A -> H) :
  set.to_Set (A ⊎ A) -> H :=
begin intro a, hinduction a with a a, exact f a, exact group.inv (f a) end

@[hott]
def word_cancel_rel_map_eq {A : Set.{u}} {H : Group.{u}} (f : A -> H) :
  Π {w₁ w₂ : Monoid_to_Set_functor.obj (word_Monoid A)} 
    (r : rel_to_cong_rel (word_cancel_rel A) w₁ w₂),
      Monoid_to_Set_functor.map (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) 
                              (Group.to_Monoid H) (group_gen_to_monoid_gen_map f)).1 w₁ =
      Monoid_to_Set_functor.map (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) 
                              (Group.to_Monoid H) (group_gen_to_monoid_gen_map f)).1 w₂ :=
begin
  intros w₁ w₂ rel, hinduction rel with rel, hinduction rel,
  { revert r, fapply word_cancel_rel.rec,
    { intros a b r, change a = b at r, rwr r,
      have p : [sum.inl b, sum.inr b] = @has_mul.mul _ (list_has_mul _) 
                                               [sum.inl b] [sum.inr b], from idp, 
      rwr p, rwr (monoid_hom_laws _).mul_comp,
      have q : ([] : Monoid_to_Set_functor.obj (word_Monoid A)) = 
                @monoid.one (Monoid_to_Set_functor.obj (word_Monoid.{u u} A)) 
                                                       (lists_are_monoid _), from idp,
      rwr q, rwr (monoid_hom_laws _).one_comp,
      have ql : @is_ind_free_monoid_of.h (set.to_Set (A ⊎ A)) _ 
                       (@lists_are_free_monoid _) (sum.inl b) = [sum.inl b], from idp,
      rwr <- ql,
      rwr <- (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) _ _).2,
      have qr : @is_ind_free_monoid_of.h (set.to_Set (A ⊎ A)) _ 
                       (@lists_are_free_monoid _) (sum.inr b) = [sum.inr b], from idp,
      rwr <- qr,
      rwr <- (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) _ _).2,
      change f b * group.inv (f b) = 1, apply Group_left_inv_is_right_inv (f b) }, 
    { intros a b r, change a = b at r, rwr r,
      have p : [sum.inr b, sum.inl b] = @has_mul.mul _ (list_has_mul _) 
                                               [sum.inr b] [sum.inl b], from idp, 
      rwr p, rwr (monoid_hom_laws _).mul_comp,
      have q : ([] : Monoid_to_Set_functor.obj (word_Monoid A)) = 
                @monoid.one (Monoid_to_Set_functor.obj (word_Monoid.{u u} A)) 
                                                       (lists_are_monoid _), from idp,
      rwr q, rwr (monoid_hom_laws _).one_comp,
      have ql : @is_ind_free_monoid_of.h (set.to_Set (A ⊎ A)) _ 
                       (@lists_are_free_monoid _) (sum.inl b) = [sum.inl b], from idp,
      rwr <- ql,
      rwr <- (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) _ _).2,
      have qr : @is_ind_free_monoid_of.h (set.to_Set (A ⊎ A)) _ 
                     (@lists_are_free_monoid _) (sum.inr b) = [sum.inr b], from idp,
      rwr <- qr,
      rwr <- (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) _ _).2,
      change group.inv (f b) * f b = 1, apply group.mul_left_inv (f b) } },
  { exact idp },
  { exact ih⁻¹ },
  { exact ih_r ⬝ ih_r' },
  { rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
    rwr ih_r, rwr ih_s }
end

@[hott]
def word_quot_Group_free_map {A : Set.{u}} {H : Group.{u}} (f : A -> H) : 
   word_quot_Group A ⟶ H :=
begin 
  fapply group_of_monoid_hom, 
  let R := rel_to_cong_rel (word_cancel_rel A),
  let M := word_quot_Monoid A,
  have univ_quot : is_univ_monoid_quotient R M, from 
              monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot, 
  fapply λ f rel_eq, (is_univ_monoid_quotient.factors univ_quot f rel_eq).1,
  { exact (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) (Group.to_Monoid H) 
                                                     (group_gen_to_monoid_gen_map f)).1 },
  { intros w₁ w₂ r, exact word_cancel_rel_map_eq f r }  
end 

@[hott]
def word_quot_Group_unique {A : Set.{u}} : Π {H : Group} (g₁ g₂ : word_quot_Group A ⟶ H),
    (Π (a : A), Group_to_Set_functor.map g₁
           (set.set_class_of (λ (a b : ↥(Monoid_to_Set_functor.obj (word_Monoid A))), 
                  rel_to_cong_rel (word_cancel_rel A) a b) [sum.inl a]) =
         Group_to_Set_functor.map g₂
           (set.set_class_of (λ (a b : ↥(Monoid_to_Set_functor.obj (word_Monoid A))), 
                  rel_to_cong_rel (word_cancel_rel A) a b) [sum.inl a])) → g₁ = g₂ :=
begin 
  let R := rel_to_cong_rel (word_cancel_rel A),
  let M := word_quot_Monoid A,
  intros H g₁ g₂ comp_eq, fapply sigma.sigma_eq, 
    { fapply @is_univ_monoid_quotient.unique (word_Monoid A) R _ (word_quot_Monoid A) 
                 (monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot),
      fapply @is_ind_free_monoid_of.unique (set.to_Set (A ⊎ A)) (word_Monoid A)
                                      (@lists_are_free_monoid (set.to_Set (A ⊎ A))),
      intro a, rwr Monoid_to_Set_functor.map_comp, 
      hinduction a with a a,
      { change Monoid_to_Set_functor.map g₁.1 _ = Monoid_to_Set_functor.map g₂.1 _,
        rwr <- Group_to_Monoid_to_Set_functor, rwr <- Group_to_Monoid_to_Set_functor,
        exact comp_eq a }, 
      { change Monoid_to_Set_functor.map g₁.1 _ = Monoid_to_Set_functor.map g₂.1 _,
        rwr <- Group_to_Monoid_to_Set_functor, rwr <- Group_to_Monoid_to_Set_functor g₂.1,
        change Group_to_Set_functor.map (group_of_monoid_hom g₁.1) 
            (@group.inv _ (word_quot_Group A).struct 
              (Monoid_to_Set_functor.map (monoid_to_univ_quotient R M 
              (Monoid_cong_quotient R).is_mon_quot).proj
                                  (lists_are_free_monoid.h (sum.inl a)))) = 
          Group_to_Set_functor.map (group_of_monoid_hom g₂.1) 
            (@group.inv _ (word_quot_Group A).struct (Monoid_to_Set_functor.map 
            (monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot).proj
                                              (lists_are_free_monoid.h (sum.inl a)))),
        apply λ q, group_hom_inv (group_of_monoid_hom g₁.fst) (Monoid_to_Set_functor.map 
                 (monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot).proj
                                 (lists_are_free_monoid.h (sum.inl a))) ⬝ q,
        apply λ q, (ap (@group.inv _ H.struct) (comp_eq a)) ⬝ q,
        apply eq.inverse, apply λ q, (group_hom_inv g₂ (Monoid_to_Set_functor.map 
             (monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot).proj
                                              (lists_are_free_monoid.h (sum.inl a)))) ⬝ q, 
        exact idp } },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

@[hott]  --[GEVE]
def word_quot_Group_is_ind_free_group (A : Set.{u}) : 
  is_ind_free_group_of A (word_quot_Group A) :=
begin 
  let R := rel_to_cong_rel (word_cancel_rel A),
  let M := word_quot_Monoid A,
  fapply is_ind_free_group_of.mk,
  { intro a, exact set.set_class_of _ [sum.inl a] },
  { intros H f, fapply dpair,
    { exact word_quot_Group_free_map f },
    { intro a, change f a = Group_to_Set_functor.map (group_of_monoid_hom _) _,  
      rwr Group_to_Monoid_to_Set_functor, 
      change A -> Monoid_to_Set_functor.obj (Group.to_Monoid H) at f,
      change f a = Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map 
            (monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot).proj _),
      rwr <- Monoid_to_Set_map_comp, rwr <- Monoid_to_Set_functor.map_comp,
      rwr <- ((monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot).factors _ _).2, 
      have ql : @is_ind_free_monoid_of.h (set.to_Set (A ⊎ A)) _ 
                  (@lists_are_free_monoid _) (sum.inl a) = [sum.inl a], from idp,
      rwr <- ql, 
      rwr <- (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) _ _).2 } },
  { intro H, apply word_quot_Group_unique }
end 

/- A subgroup is a subobject in the category of groups. The embedding monomorphism is
   a monomorphism of the underlying sets. So we can construct a subgroup as a subset of a 
   group inheriting the group structure. -/
@[hott]  --[GEVE]
def Subgroup (G : Group) := @subobject Group_Category G

@[hott, instance]
def subgroup_has_hom (G : Group) : has_hom (Subgroup G) :=
  by change has_hom (@subobject Group_Category G); apply_instance

@[hott]  --[GEVE]
def group_mon_is_inj {G H : Group} : Π (f : G ⟶ H), 
  @is_mono Group_Category _ _ f <-> 
  @set.is_set_injective (Group_to_Set_functor.obj H) (Group_to_Set_functor.obj G) 
                        (Group_to_Set_functor.map f) :=
begin 
  intro f, fapply prod.mk,
  { intro mono_f, apply mono_is_set_inj, intros A g₁ g₂ g_eq,
    let h := to_hom_set (word_quot_Group_is_ind_free_group A).h, 
    let g₁' := ((word_quot_Group_is_ind_free_group A).map g₁).1,
    let g₂' := ((word_quot_Group_is_ind_free_group A).map g₂).1,
    have hom_eq₁ : h ≫ Group_to_Set_functor.map (g₁' ≫ f) = 
                                            h ≫ Group_to_Set_functor.map (g₂' ≫ f), from 
    begin
      rwr Group_to_Set_functor.map_comp, rwr Group_to_Set_functor.map_comp,
      apply eq_of_homotopy, intro a, 
      change Group_to_Set_functor.map f (Group_to_Set_functor.map g₁' 
                                         ((word_quot_Group_is_ind_free_group A).h _)) = 
             Group_to_Set_functor.map f (Group_to_Set_functor.map g₂' 
                                         ((word_quot_Group_is_ind_free_group A).h _)),
      rwr <- ((word_quot_Group_is_ind_free_group A).map g₁).2 a,
      rwr <- ((word_quot_Group_is_ind_free_group A).map g₂).2 a,  
      exact ap10 g_eq a
    end,
    have hom_eq₂ : g₁' = g₂', from 
    begin
      fapply mono_f, fapply (word_quot_Group_is_ind_free_group A).unique, intro a, 
      change (h ≫ Group_to_Set_functor.map (g₁' ≫ f)) a = 
                                             (h ≫ Group_to_Set_functor.map (g₂' ≫ f)) a,
      exact ap10 hom_eq₁ a
    end,
    apply eq_of_homotopy, intro a, 
    rwr ((word_quot_Group_is_ind_free_group A).map g₁).2 a,
    rwr ((word_quot_Group_is_ind_free_group A).map g₂).2 a,
    change Group_to_Set_functor.map g₁' _ = Group_to_Set_functor.map g₂' _,
    rwr hom_eq₂ },
  { intro set_inj, 
    fapply λ H, @mono_is_faithful Group_Category Set_Category Group_to_Set_functor H _ _ f, 
    apply Group_to_Set_functor_is_faithful, apply set_inj_is_mono _ set_inj }
end

@[hott]
def unit_subgroup (G : Group): Subgroup G :=
begin  
  fapply subobject.mk, exact unit_Group, exact init_group_hom G, 
  intros H f₁ f₂ f_eq, fapply Group_to_Set_functor_is_faithful,
  apply eq_of_homotopy, intro h, exact @is_prop.elim _ One_is_prop _ _
end

@[hott]
def subset_of_subgroup {G : Group} (H : Subgroup G) : 
  Subset (Group_to_Set_functor.obj G) :=
λ g, image (Group_to_Set_functor.map H.hom) g 

@[hott]
structure subgroup_str {G : Group} (H : Subset (Group_to_Set_functor.obj G)) :=
  (one : group.one G ∈ H)
  (mul : Π {g₁ g₂ : G}, g₁ ∈ H -> g₂ ∈ H -> g₁ * g₂ ∈ H)
  (inv : Π {g : G}, g ∈ H -> g⁻¹ ∈ H)

@[hott]
def subgroup_laws {G : Group} (H : Subgroup G) : subgroup_str (subset_of_subgroup H) :=
begin
  fapply subgroup_str.mk,
  { apply tr, fapply fiber.mk, exact 1, exact (group_hom_laws _).one_comp },
  { intros g₁ g₂ g₁_el g₂_el, hinduction g₁_el with fib₁, hinduction g₂_el with fib₂,
    apply tr, fapply fiber.mk, exact fib₁.1 * fib₂.1, rwr (group_hom_laws _).mul_comp,
    rwr fib₁.2, rwr fib₂.2 },
  { intros g g_el, hinduction g_el with fib, 
    apply tr, fapply fiber.mk, exact fib.1⁻¹, rwr group_hom_inv, rwr fib.2 }
end 

@[hott]
def subgroup_hom_of_subset {G : Group} (H₁ H₂ : Subgroup G) :
  (subset_of_subgroup H₁ ⊆ subset_of_subgroup H₂) -> (H₁ ⟶ H₂) :=
begin
  intro sset, 
  have fib_h : Π h, fiber (Group_to_Set_functor.map H₂.hom) 
                                                 (Group_to_Set_functor.map H₁.hom h), from 
      λ h, set.set_inj_image_to_fiber _ ((group_mon_is_inj _).1 H₂.is_mono)  
          (Group_to_Set_functor.map H₁.hom h) (sset _ (tr (fiber.mk h idp))), 
  fapply hom_of_monos.mk, 
  { fapply group_hom.mk,  
    { intro h₁, exact (fib_h h₁).1 },
    { fapply group_hom_str.mk,
      { intros h₁ h₁', apply (group_mon_is_inj _).1 H₂.is_mono, rwr (fib_h _).2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr (fib_h _).2, rwr (fib_h _).2 },
      { apply (group_mon_is_inj _).1 H₂.is_mono, rwr (fib_h _).2,
        rwr (group_hom_laws _).one_comp, rwr (group_hom_laws _).one_comp } } },
  { apply Group_to_Set_functor_is_faithful, rwr Group_to_Set_functor.map_comp,
    apply eq_of_homotopy, intro h, 
    change Group_to_Set_functor.map _ (Group_to_Set_functor.map _ h) = 
                                                           Group_to_Set_functor.map _ h, 
    exact (fib_h _).2 }
end

@[hott]  --[GEVE]
def Subgroup_of_Subset {G : Group} (H : Subset (Group_to_Set_functor.obj G)) :
  subgroup_str H -> Subgroup G :=
begin  
  intro sg_str, fapply subobject.mk,
  { apply Group.mk H, fapply group.mk,
    { apply_instance },
    { intros h₁ h₂, exact ⟨@group.mul G G.struct h₁.1 h₂.1, sg_str.mul h₁.2 h₂.2⟩ },
    { intros h₁ h₂ h₃, apply pred_Set_eq, apply group.mul_assoc },
    { exact ⟨G.struct.one, sg_str.one⟩ },
    { intro h, apply pred_Set_eq, apply group.one_mul },
    { intro h, apply pred_Set_eq, apply group.mul_one },
    { intro h, exact ⟨@group.inv G G.struct h.1, sg_str.inv h.2⟩ },
    { intro h, apply pred_Set_eq, apply group.mul_left_inv } },
  { fapply group_hom.mk, 
    { exact pred_Set_map _ },
    { fapply group_hom_str.mk,
      { intros n₁ n₂, exact idp },
      { exact idp } } },
  { apply (group_mon_is_inj _).2, exact pred_Set_map_is_inj _ }
end

@[hott]
def unit_subgroup_is_initial {G : Group} : Π (H : Subgroup G), unit_subgroup G ⟶ H :=
begin
  intro H, apply subgroup_hom_of_subset, intros g g_el, 
  hinduction g_el with fib, hinduction fib with h h_eq, change One at h,
  have p : h = One.star, from is_prop.elim _ _, 
  have g_one : g = 1, by rwr <- h_eq,
  rwr g_one, apply tr, apply fiber.mk, exact (group_hom_laws H.hom).one_comp
end

/- Group homomorphisms have images. -/
@[hott, instance]  --[GEVE]
def group_hom_has_image {G H : Group} (f : G ⟶ H) : 
  @has_image Group_Category _ _ f :=
begin  
  fapply has_image.mk, apply tr, fapply cat_image.mk,
  { fapply Subgroup_of_Subset,
    { exact (λ h : H.carrier, image (Group_to_Set_functor.map f) h) },
    { fapply subgroup_str.mk,
      { apply tr, apply fiber.mk G.struct.one, exact (group_hom_laws f).one_comp },
      { intros h₁ h₂ h₁_el h₂_el, hinduction h₁_el with fib₁, hinduction h₂_el with fib₂,
        apply tr, apply fiber.mk (fib₁.1 * fib₂.1), 
        rwr (group_hom_laws f).mul_comp, rwr fib₁.2, rwr fib₂.2 },
      { intros h h_el, hinduction h_el with fib, 
        apply tr, fapply fiber.mk, exact has_inv.inv fib.1, 
        rwr group_hom_inv, rwr fib.2 } } },
  { fapply dpair,  
    { fapply group_hom.mk, 
      { intro m, fapply dpair, exact Group_to_Set_functor.map f m, 
        exact tr (fiber.mk m (@idp _ (Group_to_Set_functor.map f m))) },
      { fapply group_hom_str.mk,
        { intros m₁ m₂, apply pred_Set_eq, exact (group_hom_laws f).mul_comp _ _ },
        { apply pred_Set_eq, exact (group_hom_laws f).one_comp } } },
    { apply Group_to_Set_functor_is_faithful, exact idp } },
  { intros H' fac, fapply subgroup_hom_of_subset, 
    intros h el_im, change ↥(image _ _), change ↥(image _ _) at el_im,
    hinduction el_im with fib, change fiber (pred_Set_map _) h at fib,
    let p : fib.1.1 = h := fib.2,
    hinduction fib.1.2 with tr_eq m_fib, rwr <- p,
    apply tr, fapply fiber.mk, 
    { exact (Group_to_Set_functor.map fac.1) m_fib.1 }, 
    { change ((Group_to_Set_functor.map fac.fst) ≫ 
                             Group_to_Set_functor.map H'.hom) m_fib.1 = _, 
      rwr <- Group_to_Set_functor.map_comp, 
      have q : fac.1 ≫ H'.hom = f, from fac.2,
      rwr q, exact m_fib.2 } }
end

@[hott]  --[GEVE]
def gen_subgroup {G : Group} (L : Subset (Group_to_Set_functor.obj G)) :
  Subgroup G :=
@hom.image Group_Category _ _ (is_ind_free_group_of.map 
            (word_quot_Group_is_ind_free_group _) (pred_Set_map L)).1 
                               (group_hom_has_image _)

@[hott]
def gen_subgroup_min {G : Group} (L : Subset (Group_to_Set_functor.obj G)) :
  Π (H : Subgroup G), (L ⊆ (subset_of_subgroup H)) -> (gen_subgroup L ⟶ H) :=
begin
  intros H sset, fapply cat_image.univ, fapply dpair,
  { apply λ f, (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) f).1, 
    intro m, 
    exact (set.set_inj_image_to_fiber _ ((group_mon_is_inj _).1 H.is_mono) m.1 
                                                                  (sset m.1 m.2)).1 },
  { fapply is_ind_free_group_of.unique (word_quot_Group_is_ind_free_group _), intro n, 
    rwr Group_to_Set_functor.map_comp, 
    change Group_to_Set_functor.map H.hom (Group_to_Set_functor.map 
              (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) _).fst 
              (is_ind_free_group_of.h (word_quot_Group_is_ind_free_group _) n)) = _,
    rwr <- (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) _).2 n, 
    rwr <- (is_ind_free_group_of.map (word_quot_Group_is_ind_free_group _) _).2 n,
    rwr (set.set_inj_image_to_fiber _ ((group_mon_is_inj _).1 H.is_mono) n.1 
                                                                  (sset n.1 n.2)).2 }
end 

@[hott]   --[GEVE]
def kernel_subgroup {G H : Group} (f : G ⟶ H) : Subgroup G :=
begin
  fapply Subgroup_of_Subset,
  { intro g, exact to_Prop (Group_to_Set_functor.map f g = 1) },
  { fapply subgroup_str.mk,
    { exact (group_hom_laws f).one_comp },
    { intros h₁ h₂ h₁_el h₂_el, 
      have p₁ : Group_to_Set_functor.map f _ = 1, from h₁_el,
      have p₂ : Group_to_Set_functor.map f _ = 1, from h₂_el,
      calc Group_to_Set_functor.map f (h₁ * h₂) = Group_to_Set_functor.map f h₁ *
                                                    Group_to_Set_functor.map f h₂ : 
               (group_hom_laws f).mul_comp h₁ h₂
         ... = 1 * 1 : by rwr p₁; rwr p₂
         ... = 1 : group.one_mul _ },
  { intros h h_el, 
    have p : Group_to_Set_functor.map f _ = 1, from h_el,
    calc Group_to_Set_functor.map f h⁻¹ = (Group_to_Set_functor.map f h)⁻¹ : 
                                                                         group_hom_inv _ _
         ... = 1⁻¹ : by rwr p
         ... = 1 : begin apply eq.inverse, fapply Group_inverse_is_unique, 
                                                               exact group.one_mul _ end } }
end

@[hott]  --[GEVE]
def trivial_kernel_is_mono {G H : Group} (f : G ⟶ H) : 
  kernel_subgroup f = unit_subgroup G <-> @is_mono Group_Category _ _ f :=
begin
  fapply prod.mk,
  { intro ker_eq, apply (group_mon_is_inj _).2, 
    intros g₁ g₂ g_eq, change ↥G at g₁, change ↥G at g₂, rwr <- group.mul_one g₁,
    rwr <- group.mul_left_inv g₂, rwr <- group.mul_assoc, 
    apply λ p, p ⬝ (group.one_mul g₂), apply ap (λ g, g * g₂),
    have g_el : ↥((g₁ * g₂⁻¹) ∈ subset_of_subgroup (unit_subgroup G)), from 
    begin 
      rwr <- ker_eq, apply tr, fapply fiber.mk,
      { fapply dpair, exact g₁ * g₂⁻¹, change Group_to_Set_functor.map f (g₁ * g₂⁻¹) = 1, 
        rwr (group_hom_laws f).mul_comp, 
        apply λ p, p ⬝ Group_left_inv_is_right_inv (Group_to_Set_functor.map f g₂), 
        rwr g_eq, rwr group_hom_inv },
      { exact idp } 
    end,
    hinduction g_el with fib, change g₁ * g₂⁻¹ = _, rwr <- fib.2 },
  { intro mono_f, fapply subobj_antisymm, 
    { apply subgroup_hom_of_subset, intros g g_el, hinduction g_el with fib,
      induction fib with h h_eq, apply tr, fapply fiber.mk, exact One.star,
      have H : set.is_set_injective (Group_to_Set_functor.map f), from 
        (group_mon_is_inj f).1 mono_f,
      change h.1 = g at h_eq, rwr <- h_eq, apply H, change Group_to_Set_functor.map f 1 = _, 
      have p : Group_to_Set_functor.map f h.fst = 1, from h.2,
      rwr p, exact (group_hom_laws _).one_comp },
    { exact unit_subgroup_is_initial (kernel_subgroup f) } }
end

end algebra

end hott