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
  (mul_one : Π g : G, g * G.struct.one = g)
  (one_mul : Π g : G, 1 * g = g)
  (mul_left_inv : Π g : G, g⁻¹ * g = 1)

@[hott]
def group_laws (G : Group) : group_str G :=
  group_str.mk group.mul_assoc group.mul_one group.one_mul group.mul_left_inv 

/- Groups form a subcategory of the category of monoids. -/
@[hott, reducible]
def Group.to_Monoid : Group.{u} -> Monoid.{u} :=
  λ G, Monoid.mk G.carrier (monoid.mk G.struct.is_set_carrier G.struct.mul 
                     G.struct.mul_assoc G.struct.one G.struct.one_mul G.struct.mul_one)

@[hott]
def group_to_monoid {G : Group} : G -> Monoid_to_Set_functor.obj (Group.to_Monoid G) :=
  λ g, g 

@[hott]
structure group_of_mon_str (M : Monoid) :=
  (inv : M -> M) 
  (mul_left_inv : Π (a : M), (inv a * a) = 1)

@[hott]
def Group_of_Monoid (M : Monoid) : group_of_mon_str M -> Group := 
  λ str, Group.mk M.carrier (group.mk M.struct.is_set_carrier 
        M.struct.mul M.struct.mul_assoc M.struct.one M.struct.one_mul 
        M.struct.mul_one str.inv str.mul_left_inv)  

@[hott]
def Monoid_Group_Monoid_eq (M : Monoid) (M_str : group_of_mon_str M) :
  Group.to_Monoid (Group_of_Monoid M M_str) = M :=
begin 
  change Group.to_Monoid (Group.mk _ _) = _, change Monoid.mk _ _ = _, hinduction M, hinduction struct, 
  exact idp 
end

@[hott, reducible]  --[GEVE]
def Group_eqv_Monoid_inv_law : 
  Group ≃ Σ (M : Monoid.{u}), group_of_mon_str M :=
begin
  fapply equiv.mk,
  { intro G, exact dpair (Group.to_Monoid G) 
                         (group_of_mon_str.mk G.struct.inv G.struct.mul_left_inv) },
  { fapply adjointify,
    { intros M_str, hinduction M_str with M str, exact Group_of_Monoid M str },
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
  is_prop (group_of_mon_str M) :=
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
  hinduction p, fapply apd011,
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

@[hott]
def group_left_cancel {G : Group} : Π (g g₁ g₂ : G), g * g₁ = g * g₂ -> g₁ = g₂ :=
begin
  intros g g₁ g₂ g_eq, 
  rwr <- (group_laws _).one_mul g₁, rwr <- (group_laws _).one_mul g₂, 
  rwr <- (group_laws _).mul_left_inv g, rwr (group_laws _).mul_assoc, 
  rwr (group_laws _).mul_assoc, exact ap (λ g', g⁻¹ * g') g_eq
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
  fapply Group_of_Monoid, exact unit_Monoid,
  fapply group_of_mon_str.mk, 
  { exact id },
  { exact λ o, idp }
end  

/- For calculations with group homomorphisms, it is more effective to extract the laws
   of a homomorphism. -/
@[hott]
def group_to_mon_hom  {G H : Group} : (G ⟶ H) -> (Group.to_Monoid G ⟶ Group.to_Monoid H) :=
  λ f, f.1

@[hott]
def group_to_mon_hom_is_inj {G H : Group.{u}} : Π (g₁ g₂ : G ⟶ H), 
  group_to_mon_hom g₁ = group_to_mon_hom g₂ -> g₁ = g₂ := 
begin
  intros g₁ g₂ p, fapply sigma.sigma_eq, exact p, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end

@[hott]
def group_of_monoid_hom {G H : Group} : (Group.to_Monoid G ⟶ Group.to_Monoid H) ->
  (G ⟶ H) :=
λ f, dpair f true.intro

@[hott, reducible]
def Group_to_Set_functor : Group ⥤ Set :=
  concrete_forget_functor (Group.to_Monoid) ⋙ Monoid_to_Set_functor

@[hott, instance]
def Group_obj_is_group {G : Group} : group (Group_to_Set_functor.obj G) :=
begin 
  fapply group.mk, apply_instance, exact G.struct.mul, exact G.struct.mul_assoc, exact G.struct.one,
  exact G.struct.one_mul, exact G.struct.mul_one, exact G.struct.inv, exact G.struct.mul_left_inv 
end

@[hott]
def Group_to_Monoid_to_Set_functor_hty {G H : Group.{u}} : 
  Π (f : Group.to_Monoid G ⟶ Group.to_Monoid H) (g : Group_to_Set_functor.obj G), 
     Group_to_Set_functor.map (group_of_monoid_hom f) g = Monoid_to_Set_functor.map f g :=
λ f g, idp

@[hott]
def Group_to_Monoid_to_Set_functor {G H : Group.{u}} : 
  Π (f : Group.to_Monoid G ⟶ Group.to_Monoid H), 
     Group_to_Set_functor.map (group_of_monoid_hom f) = Monoid_to_Set_functor.map f :=
λ f, eq_of_homotopy (Group_to_Monoid_to_Set_functor_hty f)

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

@[hott]  --[GEVE]
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
def Group_to_Set_functor_is_faithful : is_faithful_functor (Group_to_Set_functor) :=
begin 
  fapply faithful_is_trans (concrete_forget_functor (Group.to_Monoid)), 
  { apply @concrete_forget_functor_is_faithful _ _ _ Group.to_Monoid },
  { apply Monoid_to_Set_functor_is_faithful }  
end  

@[hott]
def conjugate (G : Group) (g : G) : G ⟶ G :=
begin
  fapply group_hom.mk (λ h, g * h * g⁻¹), fapply group_hom_str.mk,
  { intros h₁ h₂, 
    rwr <- (group_laws _).mul_assoc, rwr <- (group_laws _).one_mul h₂,
    rwr <- (group_laws _).mul_assoc (g * h₁) 1, rwr (group_laws _).one_mul h₂,
    rwr <- (group_laws _).mul_left_inv g, rwr <- (group_laws _).mul_assoc (g * h₁) g⁻¹ g,
    rwr (group_laws _).mul_assoc _ g h₂, rwr (group_laws _).mul_assoc _ _ g⁻¹ },
  { change g * G.struct.one * g⁻¹ = 1, rwr (group_laws _).mul_one g, apply Group_left_inv_is_right_inv }
end

/- The unit group is a zero object of the category of groups. -/
@[hott]
def init_group_hom (G : Group) : unit_Group ⟶ G :=
begin
  fapply group_hom.mk (λ s, G.struct.one), fapply group_hom_str.mk,
  { intros m₁ m₂, change _ = group.mul _ _, rwr group.mul_one G.struct.one },
  { exact idp }
end

@[hott]
def term_group_hom (G : Group) : G ⟶ unit_Group :=
begin
  fapply group_hom.mk (λ s, unit_Group.struct.one), fapply group_hom_str.mk,
  { intros m₁ m₂, change _ = group.mul _ _, rwr group.mul_one unit_Group.struct.one },
  { exact idp }
end

@[hott, instance]
def unit_Group_is_zero : categories.colimits.zero Group :=
begin
  fapply categories.colimits.zero.mk unit_Group init_group_hom _ term_group_hom,
  { intros G f g, apply Group_to_Set_functor_is_faithful, 
    apply eq_of_homotopy, intro h, exact @is_prop.elim One _ _ _ },
  { intros G f g, apply Group_to_Set_functor_is_faithful, 
    apply eq_of_homotopy, intro h, 
    have p : h = unit_Group.struct.one, from @is_prop.elim One _ _ _,
    rwr p, exact (group_hom_laws f).one_comp ⬝ (group_hom_laws g).one_comp⁻¹ } 
end

/- We characterize free groups by their universal property. Then we construct
   a free group as the quotient of the type of lists over the set of generators and 
   their inverses, dividing out the inverseness equalities. -/
@[hott]
structure is_ind_free_group_of (A : Set) (F : Group) :=
  (h : A -> F)
  (map : Π {H : Group} (f : A -> H), Σ (g : F ⟶ H), Π (a : A), f a = 
                                                       Group_to_Set_functor.map g (h a))
  (unique : Π {H : Group} (g₁ g₂ : F ⟶ H), (Π (a : A),
      Group_to_Set_functor.map g₁ (h a) = Group_to_Set_functor.map g₂ (h a)) -> g₁ = g₂)

@[hott, reducible]
def word_Monoid (A : Set.{u}) : Monoid := List_Monoid (set.sum_Set A A)

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
  (word_Monoid A) -> (word_Monoid A) -> trunctype.{u} -1
| (sum.inl a::[sum.inr b]) [] := to_Prop (a = b)
| (sum.inr a::[sum.inl b]) [] := to_Prop (a = b)
| _                        _  := False

@[hott]
def word_cancel_rel.rec {A : Set.{u}} 
  {P : Π (a b : word_Monoid A), Type _} 
  (rec_l : Π (a b : A), (word_cancel_rel A (sum.inl a::[sum.inr b]) []) -> 
                                                          P (sum.inl a::[sum.inr b]) []) 
  (rec_r : Π (a b : A), (word_cancel_rel A (sum.inr a::[sum.inl b]) []) -> 
                                                          P (sum.inr a::[sum.inl b]) []) : 
  Π {a b : word_Monoid A}, (word_cancel_rel A a b) -> P a b :=
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
def word_quot_Monoid (A : Set.{u}) : Monoid :=
  (Monoid_cong_quotient (word_congruence A)).carrier

@[hott]
def word_quot_Monoid_inv {A : Set.{u}} : 
  word_quot_Monoid A -> word_quot_Monoid A :=
begin
  intro w, hinduction w with w, hinduction w with w,   
  { exact set.set_class_of (word_congruence A) (inv_word w) },
  { apply set.eq_of_setrel, fapply trunc.rec_on H, 
    { intro seq, fapply cong_sequence.rec_on seq,
      { fapply word_cancel_rel.rec, 
        { intros a b r, apply tr, apply cong_sequence.rel, change b = a, exact r⁻¹ },
        { intros a b r, apply tr, apply cong_sequence.rel, change b = a, exact r⁻¹ } },
      { intro a, exact relation.rel_refl (λ b c, word_congruence A b c) (inv_word a) },
      { intros a b seq cong, exact relation.rel_symm (λ b c, word_congruence A b c) cong },
      { intros a b c seq₁ seq₂ cong₁ cong₂,
        exact relation.rel_trans (λ b c, word_congruence A b c) cong₁ cong₂ },
      { intros a a' b b' seq₁ seq₂ cong₁ cong₂,
        rwr inv_mul_word, rwr inv_mul_word, hinduction cong₁, hinduction cong₂,
        apply tr, exact cong_sequence.mul a_2 a_1 } },
    { intro p, apply_instance } } 
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
def word_quot_Group (A : Set) : Group := 
begin
  fapply Group_of_Monoid,
  { exact word_quot_Monoid A },
  { fapply group_of_mon_str.mk, exact @word_quot_Monoid_inv A, exact word_quot_Monoid_inv_law A }
end

@[hott]
def map_to_word_quot_Group (A : Set.{u}) : A -> word_quot_Group A :=
  λ a, Monoid_to_Set_functor.map 
                      (Monoid_quotient.is_mon_quot (Monoid_cong_quotient (word_congruence A))).proj [sum.inl a] 

@[hott] 
def sum_map_to_word_quot_Group (A : Set.{u}) : A ⊎ A -> word_quot_Group A :=
begin
  intro sum_a, hinduction sum_a with a a,
  { exact Monoid_to_Set_functor.map 
                  (Monoid_quotient.is_mon_quot (Monoid_cong_quotient (word_congruence A))).proj [sum.inl a] },
  { exact Monoid_to_Set_functor.map 
                  (Monoid_quotient.is_mon_quot (Monoid_cong_quotient (word_congruence A))).proj [sum.inr a] }
end

@[hott]
def inv_map_to_word_quot_Group {A : Set.{u}} : Π (a : A),
  sum_map_to_word_quot_Group A (sum.inr a) = (map_to_word_quot_Group A a)⁻¹ :=
begin intro a, exact idp end

@[hott]
def group_gen_to_monoid_gen_map {A : Set} {H : Group} (f : A -> H) :
  set.to_Set (A ⊎ A) -> H :=
begin intro a, hinduction a with a a, exact f a, exact group.inv (f a) end

@[hott]
def word_cancel_rel_map_eq {A : Set} {H : Group} (f : A -> H) :
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
                @monoid.one (Monoid_to_Set_functor.obj (word_Monoid A)) 
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
                @monoid.one (Monoid_to_Set_functor.obj (word_Monoid A)) 
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
def word_Monoid_map {A : Set} {H : Group} (f : A -> H) : 
   word_Monoid A ⟶ Group.to_Monoid H :=
(@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) (Group.to_Monoid H) 
                                                     (group_gen_to_monoid_gen_map f)).1   

@[hott]
def word_quot_Monoid_free_map {A : Set} {H : Group} (f : A -> H) : 
   Σ (g : word_quot_Monoid A ⟶ Group.to_Monoid H), 
      word_Monoid_map f = (Monoid_cong_quotient (word_congruence A)).is_mon_quot.proj ≫ g :=
begin 
  let univ_quot : is_univ_monoid_quotient (word_congruence A) (word_quot_Monoid A) :=
              monoid_to_univ_quotient _ _ (Monoid_cong_quotient _).is_mon_quot,
  exact (is_univ_monoid_quotient.factors univ_quot (word_Monoid_map f) 
                                                     (λ w₁ w₂ r, word_cancel_rel_map_eq f r)) 
end 

@[hott]
def word_quot_Group_free_map {A : Set} {H : Group} (f : A -> H) : 
   word_quot_Group A ⟶ H :=
begin fapply group_of_monoid_hom, exact (word_quot_Monoid_free_map f).1 end 

@[hott]
def word_quot_Group_free_map_eq {A : Set} {H : Group} (f : A -> H) : 
  Π w, Group_to_Set_functor.map (word_quot_Group_free_map f) w = 
                                         Monoid_to_Set_functor.map (word_quot_Monoid_free_map f).1 w :=
begin intro w, change Group_to_Set_functor.map (group_of_monoid_hom _) w = _, exact idp end

@[hott]
def word_Monoid_map_inv {A : Set} {H : Group} (f : A -> H) : 
  Π (w : word_Monoid A), Monoid_to_Set_functor.map (word_Monoid_map f) (inv_word w) = 
              @group.inv (Group_to_Set_functor.obj H) _ (Monoid_to_Set_functor.map (word_Monoid_map f) w) :=
begin
  intro w, have p : word_Monoid_map f = _, from (word_quot_Monoid_free_map f).2, rwr p,
  rwr Monoid_to_Set_functor.map_comp, 
  change Monoid_to_Set_functor.map _ _ = group.inv (Monoid_to_Set_functor.map _ _),
  rwr <- word_quot_Group_free_map_eq, rwr <- word_quot_Group_free_map_eq, 
  change _ = (Group_to_Set_functor.map _ _)⁻¹, rwr <- group_hom_inv
end

@[hott]
def word_quot_Group_unique {A : Set.{u}} : Π {H : Group.{u}} (g₁ g₂ : word_quot_Group A ⟶ H),
   Group_to_Set_functor.map g₁ ∘ map_to_word_quot_Group A = 
                                            Group_to_Set_functor.map g₂ ∘ map_to_word_quot_Group A → g₁ = g₂ :=
begin
  let R := rel_to_cong_rel (word_cancel_rel A),
  let M := word_quot_Monoid A,
  intros H g₁ g₂ comp_eq, apply group_to_mon_hom_is_inj, 
  fapply @is_univ_monoid_quotient.unique (word_Monoid A) R _ _, 
  apply monoid_to_univ_quotient R M (Monoid_cong_quotient R).is_mon_quot,
  apply lists_are_free_monoid.unique, intro a, 
  rwr Monoid_to_Set_functor.map_comp, rwr Monoid_to_Set_functor.map_comp,
  hinduction a with a a,
  { change (Group_to_Set_functor.map g₁ ∘ map_to_word_quot_Group A) a = 
           (Group_to_Set_functor.map g₂ ∘ map_to_word_quot_Group A) a, rwr comp_eq },
  { change Group_to_Set_functor.map g₁ (sum_map_to_word_quot_Group A (sum.inr a)) = 
           Group_to_Set_functor.map g₂ (sum_map_to_word_quot_Group A (sum.inr a)),
    rwr inv_map_to_word_quot_Group, rwr group_hom_inv, rwr group_hom_inv, apply ap group.inv,
    apply ap10 comp_eq }
end

@[hott]  --[GEVE]
def word_quot_Group_is_ind_free_group (A : Set.{u}) : 
  is_ind_free_group_of A (word_quot_Group A) :=
begin 
  fapply is_ind_free_group_of.mk, 
  { exact map_to_word_quot_Group A }, 
  { intros H f, fapply dpair,
    { exact word_quot_Group_free_map f },
    { intro a, change _ = Group_to_Set_functor.map (group_of_monoid_hom _) (Monoid_to_Set_functor.map _ _), 
      rwr Group_to_Monoid_to_Set_functor, rwr <- Monoid_to_Set_map_comp, rwr <- Monoid_to_Set_functor.map_comp,
      rwr <- (word_quot_Monoid_free_map f).2,
      let p := (@is_ind_free_monoid_of.map _ _ (@lists_are_free_monoid _) (Group.to_Monoid H) 
                                                     (group_gen_to_monoid_gen_map f)).2, 
      exact p (sum.inl a) } }, 
  { intros H g₁ g₂ p, apply word_quot_Group_unique, apply eq_of_homotopy, apply p }
end

end algebra

end hott