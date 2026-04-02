import categories.concrete categories.sets

universes u u' v w
hott_theory

namespace hott
open is_trunc categories hott.is_equiv categories.sets

namespace algebra

set_option pp.universes true

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
def Magma.to_Set : Magma.{u} -> Set.{u} :=
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
@[hott]
def Set_Magma_str : Set.{u} -> Type u := 
  λ (carrier : Set.{u}), carrier -> carrier -> carrier

@[hott, instance]
def Set_Magma_str_is_set : Π (M : Set.{u}), is_set (Set_Magma_str M) :=
begin 
  intro M, change is_set (M.carrier -> M.carrier -> M.carrier), apply_instance
end

@[hott, instance]
def Magma_fib_hom_system : fib_hom_system Set_Magma_str :=
begin
  fapply fib_hom_system.mk,
  { intro M, apply_instance },
  { intros M str₁ str₂, fapply Set.mk (str₁ = str₂), apply_instance },
  { intros M str₁ str₂, apply_instance }
end

@[hott, instance]
def Magma_fibs_are_cat : sigma_fibs_are_cat Set_Magma_str :=
  begin fapply sigma_fibs_are_cat.mk, intros M str₁ str₂ h, exact h end

/- To construct a `concrete_sigma_system` on magmas, we need an equivalence with the 
   dependent type given by `Set_Magma_str`, factorizing the forgetful map to `Set`. -/
@[hott]
def Magma_eqv_Magma_str : (Σ (M : Set.{u}), Set_Magma_str M) ≃ Magma :=
begin
  fapply equiv.mk,
  { intro M_str, hinduction M_str with M M_str, hinduction M with M is_set_M, 
    exact Magma.mk M is_set_M M_str },
  { fapply adjointify,
    { intro M, hinduction M with M is_set_M M_str, 
      exact dpair (Set.mk M is_set_M) M_str },
    { intro M, hinduction M with M is_set_M M_str, exact idp },
    { intro M, hinduction M with M M_str, hinduction M with M is_set_M, exact idp } }
end

@[hott]
def Magma_Set_proj_homotopy : Π (M_str : Σ (M : Set.{u}), Set_Magma_str M),
  sigma.fst M_str = Magma.to_Set (Magma_eqv_Magma_str M_str) :=
begin
  intro M_str, hinduction M_str with M str, hinduction M with M is_set_M,
  exact idp
end

@[hott, instance]
def Magma_concrete_sigma_system : 
  concrete_sigma_system Magma.to_Set.{u} Set_Magma_str :=
begin
  fapply concrete_sigma_system.mk, 
  { intro M, apply λ eqv, (fiber.fiber_pr1 Set_Magma_str M)⁻¹ᵉ ⬝e eqv,
    apply λ eqv, eqv ⬝e (fiber.equiv_precompose Magma.to_Set Magma_eqv_Magma_str M),
    apply fiber_homotopy_equiv, exact Magma_Set_proj_homotopy },
  { intros M mul₁ mul₂, fapply equiv.mk,
    { intro p, change mul₁ = mul₂ at p, rwr p, exact 𝟙 _ },
    { fapply adjointify,
      { intro h, hinduction M with M is_set_M,
        hinduction h with h_ss h_eq, hinduction h_ss with h h_mul,
        change h = (idtoiso idp).hom ≫ (idtoiso idp).hom at h_eq,
        change h = 𝟙 (Set.mk M is_set_M) at h_eq,
        apply eq_of_homotopy2, intros m₁ m₂,
        change (𝟙 (Set.mk M is_set_M) : M -> M) (mul₁ _ _) = 
                                         mul₂ ((𝟙 (Set.mk M is_set_M) : M -> M) m₁)
                                              ((𝟙 (Set.mk M is_set_M) : M -> M) m₂),
        rwr <- h_eq, exact h_mul m₁ m₂ },
      { intro h, exact is_prop.elim _ _ },
      { intro h, exact is_set.elim _ _ } } }
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
def Semigroup.to_Magma : Semigroup.{u} -> Magma :=
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
def Monoid.to_Semigroup : Monoid.{u} -> Semigroup.{u} :=
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

@[hott]
def Semigroup_Monoid_str : Semigroup.{u} -> Type u := 
  λ SG, Σ (one : SG.carrier), (Π (m : SG.carrier), (one * m = m)) × 
                                                    (Π (m : SG.carrier), (m * one = m))

@[hott, instance]
def Semigroup_Monoid_str_is_set : 
  Π SG : Semigroup.{u}, is_set (Semigroup_Monoid_str SG) := 
begin 
  intro SG, change is_set Σ (one : SG.carrier), (Π (m : SG.carrier), (one * m = m)) × 
                                                (Π (m : SG.carrier), (m * one = m)),
  apply_instance 
end

@[hott, instance]
def Monoid_fib_hom_system : fib_hom_system Semigroup_Monoid_str :=
begin
  fapply fib_hom_system.mk,
  { intro M, apply_instance },
  { intros M str₁ str₂, fapply Set.mk (str₁ = str₂), apply_instance },
  { intros M str₁ str₂, apply_instance }
end

@[hott, instance]
def Monoid_fibs_are_cat : sigma_fibs_are_cat Semigroup_Monoid_str :=
  begin fapply sigma_fibs_are_cat.mk, intros M str₁ str₂ h, exact h end

@[hott, reducible]
def Semigroup_Monoid_str_eqv_Monoid : 
  (Σ (SG : Semigroup.{u}), Semigroup_Monoid_str SG) ≃ Monoid.{u} :=
begin
  fapply equiv.mk,
  { intro str, fapply Monoid.mk str.1.carrier, 
    exact monoid.mk str.1.struct.is_set_carrier str.1.struct.mul 
                    str.1.struct.mul_assoc str.2.1 str.2.2.1 str.2.2.2 },
  { fapply adjointify,
    { intro M, fapply dpair, exact Monoid.to_Semigroup M, fapply dpair, exact 1,
      fapply pair, exact M.struct.one_mul, exact M.struct.mul_one },
    { intro M, hinduction M with M M_struct, hinduction M_struct, exact idp },
    { intro str, hinduction str with SG mon_struct, hinduction SG with SG, 
      hinduction struct, hinduction mon_struct with one laws, 
      hinduction laws with one_mul mul_one, exact idp } }  
end

@[hott]
def Monoid_Semigroup_proj_homotopy : Π (M_str : Σ (M : Semigroup.{u}), 
  Semigroup_Monoid_str M), sigma.fst M_str = 
                          Monoid.to_Semigroup (Semigroup_Monoid_str_eqv_Monoid M_str) :=
begin
  intro M_str, hinduction M_str with M str, hinduction M with M sg_M,
  hinduction sg_M, exact idp
end

@[hott, instance]
def Monoid_concrete_sigma_system : 
  concrete_sigma_system Monoid.to_Semigroup.{u} Semigroup_Monoid_str :=
begin
  fapply concrete_sigma_system.mk, 
  { intro M, apply λ eqv, (fiber.fiber_pr1 Semigroup_Monoid_str M)⁻¹ᵉ ⬝e eqv,
    apply λ eqv, eqv ⬝e (fiber.equiv_precompose Monoid.to_Semigroup 
                                                      Semigroup_Monoid_str_eqv_Monoid M),
    apply fiber_homotopy_equiv, exact Monoid_Semigroup_proj_homotopy },
  { intros M str₁ str₂, fapply equiv.mk,
    { intro p, change str₁ = str₂ at p, rwr p, exact 𝟙 _ },
    { fapply adjointify,
      { hinduction str₁ with one₁ laws₁, hinduction str₂ with one₂ laws₂, 
        intro h, fapply sigma.sigma_eq,
        { hinduction M with M sg_M, hinduction sg_M with is_set_M,
          hinduction h with h_ss h_eq, hinduction h_ss with h h_one,
          change h = (idtoiso idp).hom ≫ (idtoiso idp).hom at h_eq,
          change h = 𝟙 (Semigroup.mk M (semigroup.mk is_set_M mul mul_assoc)) at h_eq,
          change h.1.1 one₁ = one₂ at h_one, change one₁ = one₂, rwr <- h_one,
          rwr h_eq },
        { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
      { intro h, exact is_prop.elim _ _ },
      { intro h, exact is_set.elim _ _ } } }
end

@[hott, instance]
def Monoid_is_cat : is_cat.{u u+1} Monoid.{u} := by apply_instance

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

@[hott]  --[GEVE]
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

@[hott]
def monoid_hom_mk_set_map {M N : Monoid} (f : M -> N) (str : monoid_hom_str f) :
  Monoid_to_Set_functor.map (monoid_hom.mk f str) = f :=
idp

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
def Monoid_to_Set_functor_is_faithful : precategories.is_faithful_functor (Monoid_to_Set_functor) :=
begin 
  fapply precategories.faithful_is_trans (concrete_forget_functor (Monoid.to_Semigroup)), 
  { apply @concrete_forget_functor_is_faithful _ _ _ Monoid.to_Semigroup },
  { fapply precategories.faithful_is_trans, 
    { apply @concrete_forget_functor_is_faithful _ _ _ Semigroup.to_Magma },
    { apply @concrete_forget_functor_is_faithful _ _ _ Magma.to_Set } }  
end  

/- We show that commutative monoids form a concrete category over the concrete category 
   `Monoid`, as a full subcategory. We show the injectivity of the projection from 
   commutative monoids to monoids via a characterisation of commutative monoids as a 
   Σ-type over monoids. -/
@[hott, reducible]
def CommMonoid.to_Monoid : CommMonoid.{u} -> Monoid :=
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
   a free monoid as the type of lists over the set of generators. -/
@[hott]
structure is_ind_free_monoid_of (A : Set.{u}) (F : Monoid.{u}) :=
  (h : A -> F)
  (map : Π {M : Monoid.{u}} (f : A -> M), Σ (g : F ⟶ M), 
                                     Π (a : A), f a = Monoid_to_Set_functor.map g (h a))
  (unique : Π {M : Monoid.{u}} (g₁ g₂ : F ⟶ M), (Π (a : A), 
      Monoid_to_Set_functor.map g₁ (h a) = Monoid_to_Set_functor.map g₂ (h a)) -> g₁ = g₂)

/- Composing the induced map from a free monoid with a monoid homomorphism. -/
@[hott]
def free_monoid_comp_hom {A : Set.{u}} {F : Monoid.{u}} {free : is_ind_free_monoid_of A F}
  {M M' : Monoid} (f : A -> M) (g : M ⟶ M') : 
  (free.map (Monoid_to_Set_functor.map g ∘ f)).1 = (free.map f).1 ≫ g :=
begin
  fapply free.unique, intro a, rwr <- (free.map (Monoid_to_Set_functor.map g ∘ f)).2, 
  rwr Monoid_to_Set_functor.map_comp, change _ = Monoid_to_Set_functor.map g _, 
  rwr <- (free.map f).2 a
end 

/- Lists of elements in a set form a set. (Also is in [sets.examples], but import fails.) -/
@[hott]
def list_code {A : Set.{u}} : list A -> list A -> Type u
| []     []      := One
| []     (a::l)  := Zero
| (a::l) []      := Zero
| (a::l) (b::l') := (a = b) × (list_code l l') 

@[hott, instance]
def list_code_is_prop {A : Set} : Π (l₁ l₂ : list A), is_prop (list_code l₁ l₂)
| []     []      := by change is_prop One; apply_instance
| []     (a::l)  := by change is_prop Zero; apply_instance
| (a::l) []      := by change is_prop Zero; apply_instance
| (a::l) (b::l') := @prod.is_trunc_prod (a = b) (list_code l l') -1 _ 
                                        (list_code_is_prop l l')

@[hott]
def list_refl {A : Set} : Π (l : list A), list_code l l
| []     := One.star
| (a::l) := ⟨idp, list_refl l⟩

@[hott]
def list_decode {A : Set} : Π (l₁ l₂ : list A), list_code l₁ l₂ -> l₁ = l₂
| []     []      := λ lc, idp 
| []     (a::l)  := λ lc, by hinduction lc
| (a::l) []      := λ lc, by hinduction lc
| (a::l) (b::l') := begin 
                      intro lc, hinduction lc, 
                      exact eq.concat (ap (λ a : A, list.cons a l) fst) 
                               (ap (λ l : list A, list.cons b l) (list_decode l l' snd)) 
                    end

@[hott, instance]
def lists_are_set (A : Set) : is_set (list A) :=
begin 
  fapply @set.encode_decode_set _ list_code list_refl list_code_is_prop, 
  intros a b cd, exact list_decode _ _ cd 
end

@[hott, reducible, instance]
def lists_are_monoid (A : Set.{u}) : monoid (list A) :=
begin
  fapply monoid.mk,
    { exact lists_are_set A },
    { exact list.append },
    { exact list_append_is_assoc },
    { exact [] },
    { intro l, exact idp },
    { exact list_append_nil }
end

@[hott, reducible]
def List_Monoid (A : Set.{u}) : Monoid :=
begin  
  fapply Monoid.mk,
  { exact list A },
  { exact lists_are_monoid A }
end

@[hott, instance]
def list_has_mul (A : Type u) [is_set A] : has_mul (list A) :=
begin 
  apply has_mul.mk, change List_Monoid (set.to_Set A) -> 
                           List_Monoid (set.to_Set A) -> List_Monoid (set.to_Set A),
  intros l₁ l₂, exact l₁ * l₂ 
end

@[hott]  --[GEVE]
def lists_are_free_monoid {A : Set.{u}} : is_ind_free_monoid_of A (List_Monoid A) :=
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
    { intro a, change f a = monoid.mul (f a) (monoid.one _), rwr monoid.mul_one } },
  { intros M g₁ g₂ p, fapply Monoid_to_Set_functor_is_faithful,
    apply eq_of_homotopy, intro l, hinduction l,
    { rwr (monoid_hom_laws g₁).one_comp, rwr (monoid_hom_laws g₂).one_comp },
    { change Monoid_to_Set_functor.map g₁ ([hd] * tl) = Monoid_to_Set_functor.map g₂ ([hd] * tl),
      rwr (monoid_hom_laws g₁).mul_comp, rwr (monoid_hom_laws g₂).mul_comp, rwr ih, rwr p } }
end 

end algebra

end hott