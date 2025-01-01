import hott.algebra.bundled hott.algebra.relation categories.sets categories.concrete

universes u u' v w
hott_theory

namespace hott
open trunc is_trunc hott.algebra hott.eq precategories categories hott.is_equiv 
     categories.sets subset hott.relation

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
structure Magma := 
  (carrier : Type u)
  (is_set_carrier : is_set carrier)
  (mul : carrier -> carrier -> carrier)

@[hott] 
instance has_coe_to_sort_Magma : has_coe_to_sort Magma := 
  ⟨_, Magma.carrier⟩

@[hott, instance]
def Magma_is_set (M : Magma) : is_set M.carrier :=
  M.is_set_carrier

@[hott, instance] 
def Magma_has_mul (M : Magma.{u}) : has_mul M :=
  has_mul.mk M.mul  

/- The projection map. -/
@[hott, reducible]
def Magma.to_Set : Magma.{u} -> Set_Category.{u} :=
  λ M : Magma, trunctype.mk M.carrier M.is_set_carrier

/- The homomorphism system over the projection map. -/
@[hott, reducible, instance]
def Magma_hom_system : concrete_hom_system Magma.to_Set.{u} := 
begin 
  fapply concrete_hom_system.mk, 
  { intros A B, intro f, fapply trunctype.mk, 
    { exact ∀ a₁ a₂ : A.carrier, f (a₁ * a₂) = f a₁ * f a₂ }, 
    { apply_instance } },
  { intro A, intros a₁ a₂, exact idp }, 
  { intros A B C g h el_g el_h a₁ a₂, change h (g _) = h (g _) * h (g _), 
    rwr el_g, rwr el_h },
  { intros A B g gih el_g b₁ b₂, 
    change gih.inv ((𝟙 (Magma.to_Set B) : B.carrier -> B.carrier) b₁ * 
                    (𝟙 (Magma.to_Set B) : B.carrier -> B.carrier) b₂) = _,
    rwr <- ap10 gih.r_inv b₁, rwr <- ap10 gih.r_inv b₂, change gih.inv (g _ * g _) = _, 
    rwr <- el_g, change (g ≫ gih.inv) _ = _, rwr gih.l_inv }
end

/- Descriptions of the fibers of `Magma.to_Set` as a Σ-type: the object system. -/
@[hott, reducible] 
def Magma_sigma_equiv : 
  Magma.{u} ≃ Σ (carrier : Set.{u}), carrier -> carrier -> carrier :=
begin
  fapply equiv.mk,
  { intro M, exact ⟨Magma.to_Set M, M.mul⟩ },
  { fapply adjointify, 
    { intro M_mul, exact Magma.mk M_mul.1.carrier M_mul.1.struct M_mul.2 },
    { intro M_mul, hinduction M_mul with M mul, hinduction M, exact idp },
    { intro A, hinduction A, exact idp } }
end

@[hott, reducible, instance]
def Magma_obj_system : concrete_obj_system Magma.to_Set.{u} 
      (λ A : Set_Category.{u}, A.carrier -> A.carrier -> A.carrier) :=
begin
  fapply concrete_obj_system.mk,
  fapply concrete_equiv.mk, 
  { exact Magma_sigma_equiv⁻¹ᵉ },
  { intro M_mul, hinduction M_mul with M mul, hinduction M, exact idp }
end

/- Magmas over the same set are categories, via the characterisation of Magmas as Σ-type. -/
@[hott, instance]
def Magma_fibs_are_cat : 
  sigma_fibs_are_cat (λ A : Set_Category.{u}, A.carrier -> A.carrier -> A.carrier) :=
begin
  fapply sigma_fibs_are_cat.mk, 
  { intros A mul₁ mul₂ h h_eq,
    apply eq_of_homotopy2, intros a b,
    change (𝟙 A : A.carrier -> A.carrier) (mul₁ a b) = 
              mul₂ ((𝟙 A : A.carrier -> A.carrier) a) ((𝟙 A : A.carrier -> A.carrier) b),
    rwr <- h_eq,
    have p : (concrete_full_hom_equiv (concrete_obj_system.fib_eqv Magma.to_Set 
        (λ (A : ↥Set_Category), A.carrier → A.carrier → A.carrier))).map h.1 = h.1, from
    begin 
      hinduction A with A A_set, change 𝟙 _ ≫ _ ≫ 𝟙 _ = _, rwr is_precat.comp_id 
    end,  
    rwr <- p, exact h.2 a b },
  { intros A mul, exact is_prop.elim _ _ }
end

@[hott, instance]
def Magma_is_cat : is_cat Magma.{u} := 
  by apply_instance

@[hott]
def Magma_Category : Category :=
  Category.mk Magma.{u} Magma_is_cat 

/- We show that semigroups form a concrete category over the concrete category `Magma`, 
   as a full subcategory. We show the injectivity of the projection from semigroups to 
   magmas via a characterisation of semigroups as a Σ-type over magmas. -/
@[hott, reducible]
def Semigroup.to_Magma : Semigroup.{u} -> Magma_Category :=
  λ SG, Magma.mk SG.carrier SG.struct.is_set_carrier SG.struct.mul

@[hott, reducible]
def Semigroup_eqv_Magma_mul_assoc : 
  Semigroup ≃ Σ (M : Magma.{u}), Π (a b c : M.carrier), (a * b) * c = a * (b * c) :=
begin
  fapply equiv.mk,
  { intro SG, exact dpair (Semigroup.to_Magma SG) SG.struct.mul_assoc },
  { fapply adjointify,
    { intro M, exact Semigroup.mk M.1.carrier (semigroup.mk M.1.is_set_carrier M.1.mul M.2) },
    { intro M_mul_ass, hinduction M_mul_ass with M mul_assoc, 
      hinduction M with M M_set M_mul, exact idp },
    { intro SG, hinduction SG with SG SG_struct, 
      hinduction SG_struct with is_set_SG mul_SG mul_assoc, exact idp } }
end

@[hott, instance]
def Semigroup_to_Magma_is_inj : is_injective Semigroup.to_Magma :=
begin
  fapply equiv_map_is_injective Semigroup.to_Magma sigma.fst Semigroup_eqv_Magma_mul_assoc,
  { apply eq_of_homotopy, intro SG, exact idp },
  { apply prop_fiber_is_inj, intro M, 
    fapply is_trunc_is_equiv_closed_rev -1 (fiber.fiber_pr1 _ _).to_fun, 
    { apply_instance }, 
    { apply_instance } }
end

@[hott, instance]
def Semigroup_is_cat : is_cat Semigroup := 
  full_subcat_is_cat Semigroup.to_Magma

@[hott]
def Semigroup_Category : Category :=
  Category.mk Semigroup.{u} Semigroup_is_cat

/- Monoids extend semigroups by a one-element satisfying the usual laws. -/
@[hott, reducible, hsimp]
def Monoid.to_Semigroup : Monoid.{u} -> Semigroup_Category.{u} :=
  λ M, Semigroup.mk M (monoid.to_semigroup M)

@[hott, reducible, instance]
def Monoid_hom_system : concrete_hom_system Monoid.to_Semigroup.{u} :=
begin
  fapply concrete_hom_system.mk,
  { intros M N h, fapply @trunctype.mk -1, 
    exact h.1.1 1 = 1, apply_instance },
  { intro M, exact idp },
  { intros M₁ M₂ M₃ f g f_el g_el, change g.1.1 (f.1.1 1) = 1, 
    change f.1.1 1 = 1 at f_el, rwr f_el, change g.1.1 1 = 1 at g_el, rwr g_el },
  { intros M N g g_iso g_el, change g_iso.inv.1.1 1 = 1, change g.1.1 1 = 1 at g_el,
    rwr <- g_el, change (g ≫ g_iso.inv).1.1 1 = 1, rwr g_iso.l_inv }
end

@[hott, reducible]
def Monoid_eqv_Semigroup_one_laws : Monoid.{u} ≃ 
  Σ (SG : Semigroup.{u}) (one : SG), (Π (m : SG), (one * m = m)) × 
                                     (Π (m : SG), (m * one = m)) :=
begin
  fapply equiv.mk,
  { intro M, fapply dpair, exact Monoid.to_Semigroup M, fapply dpair, exact 1,
    fapply pair, exact M.struct.one_mul, exact M.struct.mul_one },
  { fapply adjointify,
    { intro SG_struct, fapply Monoid.mk SG_struct.1.carrier, 
      exact monoid.mk SG_struct.1.struct.is_set_carrier SG_struct.1.struct.mul 
                      SG_struct.1.struct.mul_assoc SG_struct.2.1 SG_struct.2.2.1 
                      SG_struct.2.2.2 },
    { intro SG_struct, hinduction SG_struct with SG mon_struct, hinduction SG with SG, 
      hinduction struct, hinduction mon_struct with one laws, 
      hinduction laws with one_mul mul_one, exact idp },
    { intro M, hinduction M with M M_struct, hinduction M_struct, exact idp } }  
end

@[hott, reducible, instance]
def Monoid_obj_system : concrete_obj_system Monoid.to_Semigroup.{u} 
  (λ (SG : Semigroup_Category.{u}), Σ (one : SG.carrier), (Π (m : SG.carrier), 
                               (one * m = m)) × (Π (m : SG.carrier), (m * one = m))) :=
begin
  fapply concrete_obj_system.mk,
  fapply concrete_equiv.mk, exact Monoid_eqv_Semigroup_one_laws⁻¹ᵉ,
  intro SG_mon, hinduction SG_mon with SG one_laws, change SG = _, 
  hinduction SG with SG, hinduction struct, exact idp
end

@[hott, instance]
def Monoid_sigma_fibs_are_cat : sigma_fibs_are_cat (λ (SG : Semigroup_Category.{u}), 
        Σ (one : SG.carrier), (Π (m : SG.carrier), (one * m = m)) × (Π (m : SG.carrier), 
                                                                       (m * one = m))) :=
begin
  fapply sigma_fibs_are_cat.mk, 
  { intros SG mon₁ mon₂ g g_eq,
    hinduction mon₁ with one₁ laws₁, hinduction mon₂ with one₂ laws₂, 
    fapply sigma.sigma_eq, 
    { have g_eq_carrier : g.1.1.1 = 𝟙 (Magma.to_Set (Semigroup.to_Magma SG)), from 
        ap sigma.fst (ap sigma.fst g_eq),
      change (𝟙 (Magma.to_Set (Semigroup.to_Magma SG)) : SG.carrier -> SG.carrier) one₁ = _,
      rwr <- g_eq_carrier,
      have p : (concrete_full_hom_equiv (concrete_obj_system.fib_eqv Monoid.to_Semigroup 
        (λ (SG : Semigroup_Category.{u}), Σ (one : SG.carrier), (Π (m : SG.carrier), 
             (one * m = m)) × (Π (m : SG.carrier), (m * one = m))))).map g.1 = g.1, from
      begin 
        hinduction SG with SG SG_struct, hinduction SG_struct, 
        change (𝟙 _) ≫ g.1 ≫ (𝟙 _) = _, rwr is_precat.comp_id, rwr is_precat.id_comp 
      end,
      rwr <- p, exact g.2 },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { intros SG mon, exact is_prop.elim _ _ }
end

@[hott, instance]
def Monoid_is_cat : is_cat Monoid.{u} := by apply_instance

@[hott]
def Monoid_Category : Category :=
  Category.mk Monoid.{u} Monoid_is_cat

@[hott]  --[GEVE]
def unit_Monoid : Monoid :=
begin
  fapply Monoid.mk, exact One,
  fapply monoid.mk, 
  { apply_instance }, 
  { exact λ o₁ o₂, One.star }, 
  { exact λ o₁ o₂ o₃, idp }, 
  { exact One.star }, 
  { intro a, hinduction a, exact idp },
  { intro a, hinduction a, exact idp }
end

/- For calculations with monoid homomorphisms, it is more effective to extract the laws
   of a homomorphism. -/
@[hott, reducible]
def Monoid_to_Set_functor : Monoid ⥤ Set :=
  concrete_forget_functor (Monoid.to_Semigroup) ⋙ 
  concrete_forget_functor (Semigroup.to_Magma) ⋙
  concrete_forget_functor (Magma.to_Set)

@[hott]
def Monoid_to_Set_map_comp {L M N : Monoid} (f : L ⟶ M) (g : M ⟶ N) :
  Π (l : Monoid_to_Set_functor.obj L), 
       (Monoid_to_Set_functor.map f ≫ Monoid_to_Set_functor.map g) l =
        Monoid_to_Set_functor.map g (Monoid_to_Set_functor.map f l) := 
λ l, idp 

@[hott, instance]
def Monoid_Set_has_mul (M : Monoid) : has_mul (Monoid_to_Set_functor.obj M) :=
begin apply has_mul.mk, change M -> M -> M, intros m₁ m₂, exact m₁ * m₂ end

@[hott]
structure monoid_hom_str {M N : Monoid} (f : M.carrier -> N.carrier) :=
  (mul_comp : Π (m₁ m₂ : M), f (m₁ * m₂) = f m₁ * f m₂)
  (one_comp : f M.struct.one = N.struct.one) 

@[hott]
def monoid_hom_laws {M N : Monoid} (f : M ⟶ N) : 
  monoid_hom_str (Monoid_to_Set_functor.map f) :=
begin
  hinduction f with f one, hinduction f with f, hinduction f with f mul,
  exact monoid_hom_str.mk mul one 
end  

@[hott]  --[GEVE]
def monoid_hom.mk {M N : Monoid} (f : M -> N) : 
  monoid_hom_str f -> (M ⟶ N) :=
λ mon_hom_str, ⟨⟨⟨f, mon_hom_str.mul_comp⟩, true.intro⟩, mon_hom_str.one_comp⟩

@[hott]  --[GEVE]
def trivial_monoid_hom (M N : Monoid) : M ⟶ N :=
begin  
  apply monoid_hom.mk (λ m, N.struct.one), fapply monoid_hom_str.mk, 
  { intros m₁ m₂, change _ = monoid.mul _ _, rwr monoid.mul_one N.struct.one },
  { exact idp }
end

@[hott]
def init_monoid_hom (M : Monoid) : unit_Monoid ⟶ M :=
begin
  fapply monoid_hom.mk (λ s, M.struct.one), fapply monoid_hom_str.mk,
  { intros m₁ m₂, change _ = monoid.mul _ _, rwr monoid.mul_one M.struct.one },
  { exact idp }
end

@[hott]  --[GEVE]
def Monoid_to_Set_functor_is_faithful : is_faithful_functor (Monoid_to_Set_functor) :=
begin 
  fapply faithful_is_trans (concrete_forget_functor (Monoid.to_Semigroup)), 
  { apply @concrete_forget_functor_is_faithful _ _ Monoid.to_Semigroup },
  { fapply faithful_is_trans, 
    { apply @concrete_forget_functor_is_faithful _ _ Semigroup.to_Magma },
    { apply @concrete_forget_functor_is_faithful _ _ Magma.to_Set } }  
end  

/- We show that commutative monoids form a concrete category over the concrete category 
   `Monoid`, as a full subcategory. We show the injectivity of the projection from 
   commutative monoids to monoids via a characterisation of commutative monoids as a 
   Σ-type over monoids. -/
@[hott, reducible]
def CommMonoid.to_Monoid : CommMonoid.{u} -> Monoid_Category :=
  λ CM, Monoid.mk CM (comm_monoid.to_monoid CM)

@[hott, reducible]
def CommMonoid.mk' (M : Monoid.{u}) (mul_comm : Π (a b : M.carrier), a * b = b * a) :
  CommMonoid :=
CommMonoid.mk M.carrier (comm_monoid.mk M.struct.is_set_carrier M.struct.mul 
              M.struct.mul_assoc M.struct.one M.struct.one_mul M.struct.mul_one mul_comm)

@[hott, reducible]
def CommMonoid_eqv_Monoid_comm : 
  CommMonoid ≃ Σ (M : Monoid.{u}), Π (a b : M.carrier), a * b = b * a :=
begin
  fapply equiv.mk,
  { intro CM, exact dpair (CommMonoid.to_Monoid CM) CM.struct.mul_comm },
  { fapply adjointify,
    { intro M, exact CommMonoid.mk' M.1 M.2 },
    { intro M_comm, hinduction M_comm with M mul_comm, fapply sigma.sigma_eq,
      { hinduction M with M struct_M, hinduction struct_M, exact idp },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intro SG, hinduction SG with SG SG_struct, 
      hinduction SG_struct with is_set_SG mul_SG mul_assoc, exact idp } }
end

@[hott, instance]
def CommMonoid_to_Monoid_is_inj : is_injective CommMonoid.to_Monoid :=
begin
  fapply equiv_map_is_injective CommMonoid.to_Monoid sigma.fst CommMonoid_eqv_Monoid_comm,
  { apply eq_of_homotopy, intro CM, exact idp },
  { apply prop_fiber_is_inj, intro M, 
    fapply is_trunc_is_equiv_closed_rev -1 (fiber.fiber_pr1 _ _).to_fun, 
    { apply_instance }, 
    { apply_instance } }
end

@[hott, instance]
def CommMonoid_is_cat : is_cat CommMonoid := 
  full_subcat_is_cat CommMonoid.to_Monoid

@[hott]
def CommMonoid_Category : Category :=
  Category.mk CommMonoid.{u} CommMonoid_is_cat

@[hott]  --[GEVE]
def unit_CommMonoid : CommMonoid :=
begin 
  fapply CommMonoid.mk', exact unit_Monoid, 
  intros a b, hinduction a, hinduction b, exact idp 
end

@[hott]  --[GEVE]
def trivial_comm_monoid_hom (M N : CommMonoid) : M ⟶ N :=
begin  
  fapply dpair,
  { fapply monoid_hom.mk, 
    { intro m, exact N.struct.one },
    { fapply monoid_hom_str.mk, 
      { intros m₁ m₂, change _ = comm_monoid.mul _ _, rwr comm_monoid.mul_one N.struct.one },
      { exact idp } } },
  { exact true.intro }
end

end algebra

end hott