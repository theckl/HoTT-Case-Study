import hott.algebra.group hott.arity sets.subset categories.sets categories.concrete
       hott.algebra.bundled sets.product hott.algebra.relation sets.quotients

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

/- We characterize free monoids by the recursion principle and by their freely generating
   constructors, and show that these characterisations imply each other. Then we construct
   a free monoid as a HIT and as the type of lists over the set of generators. -/
@[hott]
structure is_ind_free_monoid_of (A : Set) (F : Monoid) :=
  (h : A -> F)
  (map : Π {M : Monoid} (f : A -> M), Σ (g : F ⟶ M), f = Monoid_to_Set_functor.map g ∘ h)
  (unique : Π {M : Monoid} (g₁ g₂ : F ⟶ M), 
                  Monoid_to_Set_functor.map g₁ ∘ h = Monoid_to_Set_functor.map g₂ ∘ h -> g₁ = g₂)

@[hott, reducible, instance]
def lists_are_monoid (A : Set) : monoid (list A) :=
begin
  fapply monoid.mk,
    { exact set.lists_are_set A },
    { exact list.append },
    { exact list_append_is_assoc },
    { exact [] },
    { intro l, exact idp },
    { exact list_append_nil }
end

@[hott, reducible]
def List_Monoid (A : Set) : Monoid :=
begin  
  fapply Monoid.mk,
  { exact list A },
  { exact lists_are_monoid A }
end

@[hott]
def lists_are_free_monoid {A : Set} : is_ind_free_monoid_of A (List_Monoid A) :=
begin 
  fapply is_ind_free_monoid_of.mk,
  { intro a, exact [a] },
  { intros M f, fapply dpair,
    { fapply monoid_hom.mk,  
      { intro l, hinduction l, exact M.struct.one, exact f (hd) * ih },
      { fapply monoid_hom_str.mk,
        { intros l₁ l₂, hinduction l₁, 
          { hsimp, change _ = monoid.mul _ _, rwr monoid.one_mul },
          { hsimp, change _ = monoid.mul (monoid.mul _ _) _, rwr monoid.mul_assoc,
            change _ = _ * (_ * _), rwr <- ih } },
        { exact idp } } },
    { apply eq_of_homotopy, intro a, 
      change f a = monoid.mul (f a) (monoid.one _), rwr monoid.mul_one } },
  { intros M g₁ g₂ p, fapply Monoid_to_Set_functor_is_faithful,
    apply eq_of_homotopy, intro l, hinduction l,
    { rwr (monoid_hom_laws g₁).one_comp, rwr (monoid_hom_laws g₂).one_comp },
    { change Monoid_to_Set_functor.map g₁ ([hd] * tl) = Monoid_to_Set_functor.map g₂ ([hd] * tl),
      rwr (monoid_hom_laws g₁).mul_comp, rwr (monoid_hom_laws g₂).mul_comp,
      rwr ih, change (Monoid_to_Set_functor.map g₁ ∘ (λ (a : A), [a])) hd * _ = _,
      rwr ap10 p hd } }
end 

/- We characterize and construct products of two monoids using products of the 
   underlying sets. This implies and is implied by the standard universl property. -/
@[hott]  --[GEVE]
structure is_monoid_product (M N P : Monoid) :=
  (set_prod : is_product (Monoid_to_Set_functor.obj M) 
                      (Monoid_to_Set_functor.obj N) (Monoid_to_Set_functor.obj P))
  (fst_hom : Σ (pr₁ : P ⟶ M), Monoid_to_Set_functor.map pr₁ = set_prod.fst)
  (snd_hom : Σ (pr₂ : P ⟶ N), Monoid_to_Set_functor.map pr₂ = set_prod.snd)

@[hott]  --[GEVE]
def product_monoid (M N : Monoid) : Monoid :=
begin
  fapply Monoid.mk (Monoid_to_Set_functor.obj M × Monoid_to_Set_functor.obj N),
  fapply monoid.mk,
  { apply_instance },
  { exact λ mn₁ mn₂, ⟨mn₁.1 * mn₂.1, mn₁.2 * mn₂.2⟩ },
  { intros mn₁ mn₂ mn₃, fapply pair_eq, apply monoid.mul_assoc, apply monoid.mul_assoc },
  { exact ⟨M.struct.one, N.struct.one⟩ },
  { intro mn, fapply pair_eq, apply monoid.one_mul, apply monoid.one_mul },
  { intro mn, fapply pair_eq, apply monoid.mul_one, apply monoid.mul_one }
end

@[hott]  --[GEVE]
def product_monoid_is_product (M N : Monoid) : is_monoid_product M N (product_monoid M N) :=
begin
  fapply is_monoid_product.mk, 
  { exact type_product_is_product _ _ },
  { fapply dpair, 
    { fapply monoid_hom.mk, 
      { exact prod.fst },
      { fapply monoid_hom_str.mk,
        { intros mn₁ mn₂, exact idp },
        { exact idp } } }, 
    { exact idp } },
  { fapply dpair, 
    { fapply monoid_hom.mk, 
      { exact prod.snd },
      { fapply monoid_hom_str.mk,
        { intros mn₁ mn₂, exact idp },
        { exact idp } } }, 
    { exact idp } }
end

@[hott]  --[GEVE]
structure is_univ_monoid_product (M N P : Monoid) :=
  (fst : P ⟶ M)
  (snd : P ⟶ N)
  (factors : Π {Q : Monoid} (q_M : Q ⟶ M) (q_N : Q ⟶ N), Σ (q_P : Q ⟶ P), 
               (q_P ≫ fst = q_M) × (q_P ≫ snd = q_N))
  (unique : Π {Q : Monoid} (q_P q_P' : Q ⟶ P),
               q_P ≫ fst = q_P' ≫ fst -> q_P ≫ snd = q_P' ≫ snd -> q_P = q_P')

@[hott]
def monoid_to_univ_prod_hom {M N P : Monoid} (is_prod : is_monoid_product M N P) :
  Π {Q : Monoid} (q_M : Q ⟶ M) (q_N : Q ⟶ N), Q ⟶ P :=
begin
  let is_set_prod' := (equiv_char_of_products _ _ _).1 is_prod.set_prod,
  intros Q q_M q_N, fapply monoid_hom.mk, 
  { fapply (is_set_prod'.factors _ _).1,
    exact Monoid_to_Set_functor.map q_M, exact Monoid_to_Set_functor.map q_N },
  { fapply monoid_hom_str.mk,
    {intros q₁ q₂, fapply is_prod.set_prod.pair_unique,
      { change is_set_prod'.fst _ = _,
        rwr ((is_set_prod'.factors _ _).2 (q₁ * q₂)).1,
        rwr <- is_prod.fst_hom.2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr ap10 is_prod.fst_hom.2, rwr ap10 is_prod.fst_hom.2,
        change _ = is_set_prod'.fst _ * is_set_prod'.fst _, 
        rwr ((is_set_prod'.factors _ _).2 q₁).1, 
        rwr ((is_set_prod'.factors _ _).2 q₂).1 },
      { change is_set_prod'.snd _ = _,
        rwr ((is_set_prod'.factors _ _).2 (q₁ * q₂)).2,
        rwr <- is_prod.snd_hom.2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr ap10 is_prod.snd_hom.2, rwr ap10 is_prod.snd_hom.2,
        change _ = is_set_prod'.snd _ * is_set_prod'.snd _, 
        rwr ((is_set_prod'.factors _ _).2 q₁).2, 
        rwr ((is_set_prod'.factors _ _).2 q₂).2 } }, 
    { fapply is_prod.set_prod.pair_unique,
      { change is_set_prod'.fst _ = _, rwr ((is_set_prod'.factors _ _).2 _).1,
        rwr <- is_prod.fst_hom.2,
        rwr (monoid_hom_laws _).one_comp, rwr (monoid_hom_laws _).one_comp },
      { change is_set_prod'.snd _ = _, rwr ((is_set_prod'.factors _ _).2 _).2,
        rwr <- is_prod.snd_hom.2,
        rwr (monoid_hom_laws _).one_comp, rwr (monoid_hom_laws _).one_comp } } }
end

@[hott]  --[GEVE]
def monoid_to_univ_product (M N P : Monoid) : 
  is_monoid_product M N P -> is_univ_monoid_product M N P :=
begin 
  intro is_prod, 
  let is_set_prod' := (equiv_char_of_products _ _ _).1 is_prod.set_prod,
  fapply is_univ_monoid_product.mk, 
  { exact is_prod.fst_hom.1 },
  { exact is_prod.snd_hom.1 },
  { intros Q q_M q_N, fapply dpair,
    { exact monoid_to_univ_prod_hom is_prod q_M q_N },
    { fapply prod.mk,
      { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp, 
        apply eq_of_homotopy, intro q,
        change Monoid_to_Set_functor.map is_prod.fst_hom.fst _ = _, 
        rwr ap10 is_prod.fst_hom.2, exact ((is_set_prod'.factors _ _).2 q).1 },
      { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp, 
        apply eq_of_homotopy, intro q,
        change Monoid_to_Set_functor.map is_prod.snd_hom.fst _ = _, 
        rwr ap10 is_prod.snd_hom.2, exact ((is_set_prod'.factors _ _).2 q).2 } } },
  { intros Q q_P q_P' M_eq N_eq, apply Monoid_to_Set_functor_is_faithful,  
    apply eq_of_homotopy, intro q, fapply is_prod.set_prod.pair_unique,
    { apply λ q, ap10 (is_prod.fst_hom.2)⁻¹ _ ⬝ q, apply λ q, q ⬝ ap10 is_prod.fst_hom.2 _,
      change (Monoid_to_Set_functor.map q_P ≫ Monoid_to_Set_functor.map is_prod.fst_hom.fst) q = 
             (Monoid_to_Set_functor.map q_P' ≫ Monoid_to_Set_functor.map is_prod.fst_hom.fst) q,
      rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, rwr M_eq },
    { apply λ q, ap10 (is_prod.snd_hom.2)⁻¹ _ ⬝ q, apply λ q, q ⬝ ap10 is_prod.snd_hom.2 _,
      change (Monoid_to_Set_functor.map q_P ≫ Monoid_to_Set_functor.map is_prod.snd_hom.fst) q = 
             (Monoid_to_Set_functor.map q_P' ≫ Monoid_to_Set_functor.map is_prod.snd_hom.fst) q,
      rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, rwr N_eq } }
end

@[hott]  --[GEVE]
def univ_to_monoid_product (M N P : Monoid) : 
  is_univ_monoid_product M N P -> is_monoid_product M N P :=
begin
  intro is_mon_prod, fapply is_monoid_product.mk,
  { fapply is_product.mk,
    { exact Monoid_to_Set_functor.map is_mon_prod.fst },
    { exact Monoid_to_Set_functor.map is_mon_prod.snd },
    { intros m n, fapply dpair,
      { fapply Monoid_to_Set_functor.map, exact List_Monoid One_Set, 
        { fapply (is_mon_prod.factors _ _).1,
          { apply (lists_are_free_monoid.map _).1, fapply One.rec, exact m }, 
          { apply (lists_are_free_monoid.map _).1, fapply One.rec, exact n } },
        { exact [One.star] } },
      { fapply prod.mk,
        { change (Monoid_to_Set_functor.map _ ≫ Monoid_to_Set_functor.map _) _ = _,
          rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, 
          rwr (is_mon_prod.factors _ _).2.1, 
          change (Monoid_to_Set_functor.map (lists_are_free_monoid.map _).fst ∘
                                                       lists_are_free_monoid.h) _ = m,
          rwr <- ap10 (lists_are_free_monoid.map _).2 },
        { change (Monoid_to_Set_functor.map _ ≫ Monoid_to_Set_functor.map _) _ = _,
          rwr <- ap10 (Monoid_to_Set_functor.map_comp _ _) _, 
          rwr (is_mon_prod.factors _ _).2.2, 
          change (Monoid_to_Set_functor.map (lists_are_free_monoid.map _).fst ∘
                                                       lists_are_free_monoid.h) _ = n,
          rwr <- ap10 (lists_are_free_monoid.map _).2 } } },
    { intros p p' fst_eq snd_eq, 
      let one_map_P : One_Set -> Monoid_to_Set_functor.obj P := by fapply One.rec; exact p,
      let free_hom_P : ↥(List_Monoid One_Set ⟶ P) := (lists_are_free_monoid.map one_map_P).1,
      let one_map_P' : One_Set -> Monoid_to_Set_functor.obj P := by fapply One.rec; exact p',
      let free_hom_P' : ↥(List_Monoid One_Set ⟶ P) := (lists_are_free_monoid.map one_map_P').1,
      have free_hom_eq : free_hom_P = free_hom_P', from 
      begin
        fapply is_mon_prod.unique,
        { apply lists_are_free_monoid.unique, 
          apply eq_of_homotopy, intro o, hinduction o,
          rwr Monoid_to_Set_functor.map_comp,
          change Monoid_to_Set_functor.map _ ((Monoid_to_Set_functor.map free_hom_P ∘ 
                                                               lists_are_free_monoid.h) _) = _,
          rwr <- ap10 (lists_are_free_monoid.map _).2, rwr fst_eq,
          rwr Monoid_to_Set_functor.map_comp,
          change _ = Monoid_to_Set_functor.map _ ((Monoid_to_Set_functor.map free_hom_P' ∘ 
                                                       lists_are_free_monoid.h) _),
          rwr <- ap10 (lists_are_free_monoid.map _).2 },
        { apply lists_are_free_monoid.unique, 
          apply eq_of_homotopy, intro o, hinduction o,
          rwr Monoid_to_Set_functor.map_comp,
          change Monoid_to_Set_functor.map _ ((Monoid_to_Set_functor.map free_hom_P ∘ 
                                                               lists_are_free_monoid.h) _) = _,
          rwr <- ap10 (lists_are_free_monoid.map _).2, rwr snd_eq,
          rwr Monoid_to_Set_functor.map_comp,
          change _ = Monoid_to_Set_functor.map _ ((Monoid_to_Set_functor.map free_hom_P' ∘ 
                                                       lists_are_free_monoid.h) _),
          rwr <- ap10 (lists_are_free_monoid.map _).2 }
      end,  
      have p_eq : Monoid_to_Set_functor.map free_hom_P [One.star] = p, from 
      begin 
        change ((Monoid_to_Set_functor.map free_hom_P) ∘ lists_are_free_monoid.h) _ = _, 
        rwr <- ap10 (lists_are_free_monoid.map _).2 
      end,
      have p'_eq : (Monoid_to_Set_functor.map free_hom_P') [One.star] = p', from
      begin 
        change (Monoid_to_Set_functor.map free_hom_P' ∘ lists_are_free_monoid.h) _ = _, 
        rwr <- ap10 (lists_are_free_monoid.map _).2 
      end,    
      rwr <- p_eq, rwr <- p'_eq, rwr free_hom_eq } },
  { fapply dpair is_mon_prod.fst, exact idp },
  { fapply dpair is_mon_prod.snd, exact idp }
end

/- A submonoid is a subobject in the category of monoids, but because of the faithful 
   forgetful functor to sets, the set map underlying the embedding monomorphism is also
   a monomorphism, that is, injective. So we can construct a submonoid as a subset of a 
   monoid inheriting the monoid structure. -/
@[hott]  --[GEVE]
def Submonoid (M : Monoid) := @subobject Monoid_Category M

@[hott, instance]
def submonoid_has_hom (M : Monoid) : has_hom (Submonoid M) :=
  by change has_hom (@subobject Monoid_Category M); apply_instance

@[hott]  --[GEVE]
def monoid_mon_is_inj {N M : Monoid} : Π (f : N ⟶ M), 
  @is_mono Monoid_Category _ _ f <-> 
  @set.is_set_injective (Monoid_to_Set_functor.obj M) (Monoid_to_Set_functor.obj N) 
                        (Monoid_to_Set_functor.map f) :=
begin                        
  intro f, apply prod.mk,
  { intro mono_f, intros n₁ n₂ p, 
    let g₁ : ↥(List_Monoid One_Set ⟶ N), from (lists_are_free_monoid.map (λ s, n₁)).1,
    let g₂ : ↥(List_Monoid One_Set ⟶ N), from (lists_are_free_monoid.map (λ s, n₂)).1,
    have p₁ : Monoid_to_Set_functor.map g₁ [One.star] = n₁, from 
                                    (ap10 (lists_are_free_monoid.map (λ s, n₁)).2 _)⁻¹,
    have p₂ : Monoid_to_Set_functor.map g₂ [One.star] = n₂, from 
                                    (ap10 (lists_are_free_monoid.map (λ s, n₂)).2 _)⁻¹,
    rwr <- p₁, rwr <- p₂, apply λ q, ap10 q [One.star], 
    apply ap (λ f, Monoid_to_Set_functor.map f),
    apply mono_f, apply lists_are_free_monoid.unique, 
    apply eq_of_homotopy, intro s, hinduction s, 
    change (Monoid_to_Set_functor.map _ ∘ _) _ = (Monoid_to_Set_functor.map _ ∘ _) _, 
    rwr Monoid_to_Set_functor.map_comp, rwr Monoid_to_Set_functor.map_comp,
    change Monoid_to_Set_functor.map f (Monoid_to_Set_functor.map g₁ [One.star]) = 
                    Monoid_to_Set_functor.map f (Monoid_to_Set_functor.map g₂ [One.star]),
    rwr p₁, rwr p₂, rwr p },
  { intro set_inj, 
    fapply λ H, @mono_is_faithful Monoid_Category Set_Category Monoid_to_Set_functor H 
                                  _ _ f, 
    apply Monoid_to_Set_functor_is_faithful, apply set_inj_is_mono _ set_inj }
end 

@[hott]  --[GEVE]
def Submonoid_of_Subset {M : Monoid} (N : Subset (Monoid_to_Set_functor.obj M)) : 
  @subset.elem (Monoid_to_Set_functor.obj M) M.struct.one N -> 
  (Π n₁ n₂ : N, @subset.elem (Monoid_to_Set_functor.obj M) 
                             (@monoid.mul M M.struct n₁.1 n₂.1) N) -> Submonoid M :=
begin  
  intros one_in prod_in, fapply subobject.mk,
  { apply Monoid.mk N, fapply monoid.mk,
    { apply_instance },
    { intros n₁ n₂, exact ⟨@monoid.mul M M.struct n₁.1 n₂.1, prod_in n₁ n₂⟩ },
    { intros n₁ n₂ n₃, apply pred_Set_eq, apply monoid.mul_assoc },
    { exact ⟨M.struct.one, one_in⟩ },
    { intros n, apply pred_Set_eq, apply monoid.one_mul },
    { intros n, apply pred_Set_eq, apply monoid.mul_one } },
  { fapply monoid_hom.mk, 
    { exact pred_Set_map _ },
    { fapply monoid_hom_str.mk,
      { intros n₁ n₂, exact idp },
      { exact idp } } },
  { apply (monoid_mon_is_inj _).2, exact pred_Set_map_is_inj _ }
end

@[hott]
def subset_of_submonoid {M : Monoid} (N : Submonoid M) : 
  Subset (Monoid_to_Set_functor.obj M) :=
λ m, image (Monoid_to_Set_functor.map N.hom) m 

@[hott]
def submonoid_hom_of_subset {M : Monoid} (N₁ N₂ : Submonoid M) :
  (subset_of_submonoid N₁ ⊆ subset_of_submonoid N₂) -> (N₁ ⟶ N₂) :=
begin
  intro sset, 
  have fib_n : Π n, fiber (Monoid_to_Set_functor.map N₂.hom) (Monoid_to_Set_functor.map N₁.hom n), from 
      λ n, set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N₂.is_mono)  
          (Monoid_to_Set_functor.map N₁.hom n) (sset _ (tr (fiber.mk n idp))), 
  fapply hom_of_monos.mk, 
  { fapply monoid_hom.mk,  
    { intro n₁, exact (fib_n n₁).1 },
    { fapply monoid_hom_str.mk,
      { intros n₁ n₁', apply (monoid_mon_is_inj _).1 N₂.is_mono, rwr (fib_n _).2, 
        rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
        rwr (fib_n _).2, rwr (fib_n _).2 },
      { apply (monoid_mon_is_inj _).1 N₂.is_mono, rwr (fib_n _).2,
        rwr (monoid_hom_laws _).one_comp, rwr (monoid_hom_laws _).one_comp } } },
  { apply Monoid_to_Set_functor_is_faithful, rwr Monoid_to_Set_functor.map_comp,
    apply eq_of_homotopy, intro n, 
    change Monoid_to_Set_functor.map _ (Monoid_to_Set_functor.map _ n) = 
                                                           Monoid_to_Set_functor.map _ n, 
    exact (fib_n _).2 }
end

/- Monoid homomorphisms have images. -/
@[hott, instance]  --[GEVE]
def monoid_hom_has_image {M N : Monoid} (f : M ⟶ N) : 
  @has_image Monoid_Category _ _ f :=
begin  
  fapply has_image.mk, apply tr, fapply cat_image.mk,
  { fapply Submonoid_of_Subset,
    { exact (λ b : N.carrier, image (Monoid_to_Set_functor.map f) b) },
    { apply tr, apply fiber.mk M.struct.one, exact (monoid_hom_laws f).one_comp },
    { intros n₁ n₂, hinduction n₁ with n₁ im₁, hinduction n₂ with n₂ im₂,
      hinduction im₁ with fib₁, hinduction im₂ with fib₂, 
      apply tr, apply fiber.mk (fib₁.1 * fib₂.1), 
      rwr (monoid_hom_laws f).mul_comp, rwr fib₁.2, rwr fib₂.2 } },
  { fapply dpair,  
    { fapply monoid_hom.mk, 
      { intro m, fapply dpair, exact Monoid_to_Set_functor.map f m, 
        exact tr (fiber.mk m (@idp _ (Monoid_to_Set_functor.map f m))) },
      { fapply monoid_hom_str.mk,
        { intros m₁ m₂, apply pred_Set_eq, exact (monoid_hom_laws f).mul_comp _ _ },
        { apply pred_Set_eq, exact (monoid_hom_laws f).one_comp } } },
    { apply Monoid_to_Set_functor_is_faithful, exact idp } },
  { intros N' fac, fapply submonoid_hom_of_subset, 
    intros n el_im, change ↥(image _ _), change ↥(image _ _) at el_im,
    hinduction el_im with fib, change fiber (pred_Set_map _) n at fib,
    let p : fib.1.1 = n := fib.2,
    hinduction fib.1.2 with tr_eq m_fib, rwr <- p,
    apply tr, fapply fiber.mk, 
    { exact (Monoid_to_Set_functor.map fac.1) m_fib.1 }, 
    { change ((Monoid_to_Set_functor.map fac.fst) ≫ 
                             Monoid_to_Set_functor.map N'.hom) m_fib.1 = _, 
      rwr <- Monoid_to_Set_functor.map_comp, 
      have q : fac.1 ≫ N'.hom = f, from fac.2,
      rwr q, exact m_fib.2 } }
end

@[hott]  --[GEVE]
def gen_submonoid {M : Monoid} (L : Subset (Monoid_to_Set_functor.obj M)) :
  Submonoid M :=
@hom.image Monoid_Category _ _ (lists_are_free_monoid.map (pred_Set_map L)).1 
                               (monoid_hom_has_image _)

@[hott]
def gen_submonoid_min {M : Monoid} (L : Subset (Monoid_to_Set_functor.obj M)) :
  Π (N : Submonoid M), (L ⊆ (subset_of_submonoid N)) -> (gen_submonoid L ⟶ N) :=
begin
  intros N sset, fapply cat_image.univ, fapply dpair,
  { apply λ f, (lists_are_free_monoid.map f).1, intro m, 
    exact (set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N.is_mono) m.1 
                                                                  (sset m.1 m.2)).1 },
  { fapply lists_are_free_monoid.unique, apply eq_of_homotopy, intro n, 
    rwr Monoid_to_Set_functor.map_comp, 
    change Monoid_to_Set_functor.map N.hom ((Monoid_to_Set_functor.map 
              (lists_are_free_monoid.map _).fst ∘ lists_are_free_monoid.h) n) = _,
    rwr <- ap10 (lists_are_free_monoid.map _).2 n,
    rwr <- ap10 (lists_are_free_monoid.map _).2 n,
    rwr (set.set_inj_image_to_fiber _ ((monoid_mon_is_inj _).1 N.is_mono) n.1 
                                                                  (sset n.1 n.2)).2 }
end 

@[hott]  --[GEVE]
def kernel_pair_submon {M N : Monoid} (f : M ⟶ N) : Submonoid (product_monoid M M) :=
begin
  let f' := Monoid_to_Set_functor.map f,
  fapply Submonoid_of_Subset,
  { intro m, exact to_Prop (f' m.1 = f' m.2) },
  { exact idp },
  { intros m₁ m₂, change Monoid_to_Set_functor.map f (m₁.1.1 * m₂.1.1) = 
                         Monoid_to_Set_functor.map f (m₁.1.2 * m₂.1.2), 
    rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
    change f' _ * f' _ = f' _ * f' _,
    have fst_eq : f' m₁.1.1 = f' m₁.1.2, from m₁.2,
    have snd_eq : f' m₂.1.1 = f' m₂.1.2, from m₂.2,
    rwr fst_eq, rwr snd_eq }
end

/- We construct quotients of monoids as quotients of the underlying set by a congruence,
   with the induced monoid structure. Then we characterize monoid quotients by the 
   universal property. -/
@[hott]  --[GEVE]
class is_monoid_congruence {M : Monoid} 
  (R : Monoid_to_Set_functor.obj M -> Monoid_to_Set_functor.obj M -> Prop)
  extends (is_equivalence (λ m n : Monoid_to_Set_functor.obj M, R m n)) :=
(mul_comp : Π (m m' n n' : Monoid_to_Set_functor.obj M), R m m' -> R n n' -> 
                                                                     R (m * n) (m' * n'))

@[hott]
def kernel_pair_to_rel {M N : Monoid} (f : M ⟶ N) : 
  Monoid_to_Set_functor.obj M -> Monoid_to_Set_functor.obj M -> Prop :=
λ m₁ m₂, to_Prop (Monoid_to_Set_functor.map f m₁ = Monoid_to_Set_functor.map f m₂)

@[hott]
def kernel_pair_to_cong {M N : Monoid} (f : M ⟶ N) : 
  is_monoid_congruence (kernel_pair_to_rel f) :=
begin
  fapply λ H congr, @is_monoid_congruence.mk M (kernel_pair_to_rel f) H congr,
  { fapply is_equivalence.mk,
    { intro m, exact idp },
    { intros m n p, exact p⁻¹ },
    { intros m n o p q, exact p ⬝ q } },
  { intros m m' n n' rel_m rel_n, 
    change Monoid_to_Set_functor.map f (m * n) = Monoid_to_Set_functor.map f (m' * n'),
    rwr (monoid_hom_laws _).mul_comp, rwr (monoid_hom_laws _).mul_comp,
    change _ = _ at rel_m, change _ = _ at rel_n, rwr rel_m, rwr rel_n } 
end

@[hott]
def monoid_quotient {M : Monoid} 
  (R : Monoid_to_Set_functor.obj M -> Monoid_to_Set_functor.obj M -> Prop)
  [H : is_monoid_congruence R] : Σ (is_mon : monoid (set.set_quotient R)),
  @monoid_hom_str M (Monoid.mk (set.set_quotient R) is_mon) (set.set_class_of R) :=
begin
  fapply dpair,
  { fapply monoid.mk,
    { apply_instance },
    { fapply set.set_quotient.rec2, 
      { intros m₁ m₂, exact set.set_class_of R (m₁*m₂) },
      { intros m m' n rel, apply pathover_of_eq, apply set.eq_of_setrel, 
        fapply H.mul_comp, exact rel, exact is_equivalence.refl (λ m n, R m n) n },
      { intros m n n' rel, apply pathover_of_eq, apply set.eq_of_setrel, 
        fapply H.mul_comp, exact is_equivalence.refl (λ m n, R m n) m, exact rel } },
    { fapply set.set_quotient.prec3, intros m₁ m₂ m₃, apply set.eq_of_setrel, 
      have ass : m₁ * m₂ * m₃ = m₁ * (m₂ * m₃), from monoid.mul_assoc m₁ m₂ m₃, 
      rwr ass, exact is_equivalence.refl (λ m n, R m n) _ },
    { exact set.set_class_of R M.struct.one },
    { fapply set.set_quotient.prec, intro m, apply set.eq_of_setrel,
      have one_mul : monoid.one M.carrier * m = m, from monoid.one_mul m,
      rwr one_mul, exact is_equivalence.refl (λ m n, R m n) _ },
    { fapply set.set_quotient.prec, intro m, change M.carrier at m, apply set.eq_of_setrel,
      have mul_one : m * (monoid.one M.carrier) = m, from monoid.mul_one m,
      rwr mul_one, exact is_equivalence.refl (λ m n, R m n) _ } },
  { fapply monoid_hom_str.mk, 
    { intros m₁ m₂, exact idp },
    { exact idp } }
end

@[hott]
def quotient_is_monoid_to_cong {M Q : Monoid} 
  (R : Monoid_to_Set_functor.obj M -> Monoid_to_Set_functor.obj M -> Prop) 
  [H : is_equivalence (λ m n, R m n)] :
  Π (is_quot : set.is_cons_quotient R (Monoid_to_Set_functor.obj Q)),
                           (monoid_hom_str is_quot.proj) -> (is_monoid_congruence R)  :=
sorry

end algebra

end hott