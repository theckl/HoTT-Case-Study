import sets.algebra init2 types2 sets.axioms

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.equiv

/-
We introduce precategories and categories following the HoTT book, 
Sec. 9.1. HoTT precategories have sets of homomorphisms, and HoTT categories 
prescribe univalence : Isomorphisms are equivalent to identities of objects.

As far as possible we copy the mathlib-code in [category_theory.category.default]. 
In particular, we keep the distinction of universe levels for objects and 
morphisms of a category. On the other hand, we bundle the definition of 
precategories and categories, as this makes it easier to deal with questions on
their equivalence and equality.
-/

namespace precategories

/-- A 'notation typeclass' on the way to defining a precategory. -/
@[hott]
class has_hom (obj : Type u) : Type (max u (v+1)) :=
  (hom : obj → obj → Set.{v})

infixr ` ⟶ `:10 := has_hom.hom  -- type as \h

/- A characterisation of equality of hom-structures. -/
@[hott, reducible]
def has_hom_eqv_hom {C : Type _} : (has_hom C) ≃ (C -> C -> Set) :=
begin
  fapply equiv.mk,
  { intro hh, exact @has_hom.hom _ hh },
  { fapply adjointify,
    { intro h, exact has_hom.mk h },
    { intro h, refl },
    { intro hh, hinduction hh, refl } }
end

@[hott, reducible]
def has_hom_eq_eqv_hom_eq {C : Type _} (hh₁ hh₂ : has_hom C) :
  (hh₁ = hh₂) ≃ ((@has_hom.hom _ hh₁) = (@has_hom.hom _ hh₂)) :=
eq_equiv_fn_eq_of_equiv has_hom_eqv_hom hh₁ hh₂ 

@[hott, reducible]
def hom_eqv_hom_bij {C : Type _} (h₁ h₂ : C -> C -> Set) :
  (h₁ = h₂) ≃ (Π x y : C, bijection (h₁ x y) (h₂ x y)) :=
begin
  fapply equiv.mk,
  { intro h_eq, intros x y, exact set_eq_to_bij (ap100 h_eq x y) },
  { fapply adjointify,
    { intro hom_bij, fapply eq_of_homotopy2, intros x y,
      exact bij_to_set_eq (hom_bij x y) },
    { intro hom_bij, apply eq_of_homotopy2, intros x y, hsimp,
      rwr ap100_eq_of_hty2_inv, hsimp, 
      exact is_equiv.right_inv (set_eq_to_bij) (hom_bij x y) },
    { intro h_eq, hsimp, 
      apply λ r, r ⬝ (hty2_of_ap100_eq_inv h_eq), 
      apply ap eq_of_homotopy2, apply eq_of_homotopy2, intros x y,
      exact is_equiv.left_inv (set_eq_to_bij) (ap100 h_eq x y) } }
end

@[hott]
def bij_hom_map {C : Type _} (hh₁ hh₂ : has_hom C) :=
  Π x y : C, bijection (@has_hom.hom _ hh₁ x y) 
                       (@has_hom.hom _ hh₂ x y)

@[hott, reducible]
def has_hom_eqv_bij {C : Type _} (hh₁ hh₂ : has_hom C) :
  (hh₁ = hh₂) ≃ (bij_hom_map hh₁ hh₂) :=
has_hom_eq_eqv_hom_eq hh₁ hh₂ ⬝e hom_eqv_hom_bij _ _

/- This is needed for characterising the equalities of category structures. -/
@[hott, reducible]
def bij_hom_map_id {C : Type _} (hh : has_hom C) : bij_hom_map hh hh :=
  λ x y, identity (@has_hom.hom _ hh x y)  

@[hott, reducible]
def hom_ppred {C : Type _} (hh₀ : has_hom C) : ppred hh₀ :=
  ppred.mk (λ hh : has_hom C, bij_hom_map hh₀ hh) 
           (bij_hom_map_id hh₀)

@[hott]
def is_contr_hom {C : Type _} (hh₀ : has_hom C) :
  is_contr (Σ hh : has_hom C, bij_hom_map hh₀ hh) :=
begin 
  fapply ppmap_id_eqv_tot_space_contr' (hom_ppred hh₀), 
  { intro hh, exact has_hom_eqv_bij hh₀ hh },
  { change (hom_eqv_hom_bij _ _).to_fun 
      ((has_hom_eq_eqv_hom_eq hh₀ hh₀) idp) = bij_hom_map_id hh₀,
    hsimp, apply eq_of_homotopy2, intros x y, hsimp, 
    hinduction hh₀ with h₀,
    change set_eq_to_bij (ap100 (ap (@has_hom.hom _) idp) x y) = _,
    rwr ap_idp, 
    change set_eq_to_bij (@idp _ (h₀ x y)) = identity (h₀ x y), 
    rwr idp_to_identity }
end              

/-- A preliminary structure on the way to defining a precategory,
containing the data, but none of the axioms. -/
@[hott]
class category_struct (obj : Type u) 
extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : Π a : obj, hom a a)
(comp     : Π {a b c : obj}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

/- A characterisation of equalities between category structures. -/
@[hott] 
structure cat_hom_ops {C : Type _} (hh : has_hom C) :=
  (id       : Π a : C, a ⟶ a)
  (comp     : Π {a b c : C}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c))

@[hott]
def cat_str_sig (C : Type _) := Σ (hh : has_hom C), cat_hom_ops hh

@[hott]
def cat_str_eqv_sig (C : Type _) : (category_struct C) ≃ (cat_str_sig C) :=
begin
  fapply equiv.mk,
  { intro cat_str, 
    exact dpair cat_str.to_has_hom (@cat_hom_ops.mk _ 
                   cat_str.to_has_hom cat_str.id cat_str.comp) },
  { fapply adjointify,
    { intro cat_str_sig, 
      exact @category_struct.mk _ cat_str_sig.1 cat_str_sig.2.id 
                                              cat_str_sig.2.comp },
    { intro cat_str_sig, hinduction cat_str_sig with hh hom_ops, 
      hinduction hom_ops with id comp, hsimp },
    { intro cat_str, hinduction cat_str with hh id comp, hsimp } }
end

@[hott]
structure cat_map_laws {C : Type _} {str₁ str₂ : cat_str_sig C}
  (hom_map : Π {x y : C}, (@has_hom.hom _ str₁.1 x y) → 
                               (@has_hom.hom _ str₂.1 x y)) :=
  (hom_map_id   : ∀ {x : C}, hom_map (str₁.2.id x) = (str₂.2.id x))
  (hom_map_comp : ∀ {x y z : C} (f : @has_hom.hom _ str₁.1 x y) 
                                (g : @has_hom.hom _ str₁.1 y z), 
    hom_map (str₁.2.comp f g) = str₂.2.comp (hom_map f) (hom_map g))

@[hott, instance]
def cat_map_laws_is_prop {C : Type _} {str₁ str₂ : cat_str_sig C}
  (hom_map : Π {x y : C}, (@has_hom.hom _ str₁.1 x y) → 
                                  (@has_hom.hom _ str₂.1 x y)) :
  is_prop (cat_map_laws @hom_map) :=
begin 
  fapply is_prop.mk, intros ml₁ ml₂, 
  hinduction ml₁ with mi₁ ci₁, hinduction ml₂ with mi₂ ci₂, 
  fapply ap011, 
  all_goals { exact is_prop.elim _ _ } 
end

@[hott]
def cat_idmap_laws {C : Type _} (str : cat_str_sig C) : 
  cat_map_laws (λ x y, (bij_hom_map_id str.1 x y).map) :=
cat_map_laws.mk (λ x, idp) (λ x y z f g, idp)

@[hott, reducible]
def cat_str_dep_ppred {C : Type _} (hh₀ : has_hom C) 
  (hh_ops₀ : cat_hom_ops hh₀) : dep_ppred hh₀ hh_ops₀ :=
dep_ppred.mk (hom_ppred hh₀) 
             (λ hh hh_ops bhm, @cat_map_laws _ ⟨hh₀, hh_ops₀⟩ 
                            ⟨hh, hh_ops⟩ (λ x y, (bhm x y).map)) 
             (cat_idmap_laws ⟨hh₀, hh_ops₀⟩)

@[hott, reducible] 
def cat_str_sig_iso {C : Type _} (str₁ str₂ : cat_str_sig C) :=
  Σ (bhm : bij_hom_map str₁.1 str₂.1), 
                  @cat_map_laws _ ⟨str₁.1, str₁.2⟩ ⟨str₂.1, str₂.2⟩
                                          (λ x y, (bhm x y).map)

@[hott, reducible]
def cat_str_sig_eq_eqv_iso {C : Type _} (str₁ str₂ : cat_str_sig C) :
  (str₁ = str₂) ≃ (cat_str_sig_iso str₁ str₂) :=
begin
  hinduction str₁ with hh₁ hh_ops₁,
  fapply struct_id_char_of_contr hh_ops₁ 
                        (cat_str_dep_ppred hh₁ hh_ops₁) _ _ str₂,
  { exact is_contr_hom hh₁ },
  { hsimp, fapply is_contr.mk,
    { exact ⟨hh_ops₁, cat_idmap_laws ⟨hh₁, hh_ops₁⟩⟩ },
    { intro cat_hom_map, hinduction cat_hom_map with hom_ops hom_laws,
      hinduction hh_ops₁ with id₁ comp₁, hinduction hom_ops with id comp,
      fapply sigma.sigma_eq, 
      { hsimp, fapply ap011 cat_hom_ops.mk, 
        { apply eq_of_homotopy, exact hom_laws.hom_map_id },
        { apply eq_of_homotopy3, intros x y z, 
          apply eq_of_homotopy2, intros f g, 
          exact hom_laws.hom_map_comp f g } },
      { hsimp, apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end

@[hott, reducible]
def cat_str_eq_eqv_iso {C : Type _} 
  (str₁ str₂ : category_struct C) :
  (str₁ = str₂) ≃ (cat_str_sig_iso (cat_str_eqv_sig C str₁) 
                                   (cat_str_eqv_sig C str₂)) :=
eq_equiv_fn_eq_of_equiv (cat_str_eqv_sig C) _ _ ⬝e
cat_str_sig_eq_eqv_iso _ _

/-- The structure of a precategory. -/
@[hott, class]
structure is_precat (obj : Type u) 
extends category_struct.{v} obj : Type (max u (v+1)) :=
(id_comp : ∀ {a b : obj} (f : hom a b), 𝟙 a ≫ f = f)
(comp_id : ∀ {a b : obj} (f : hom a b), f ≫ 𝟙 b = f)
(assoc   : ∀ {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d),
  (f ≫ g) ≫ h = f ≫ (g ≫ h))

attribute [hsimp] is_precat.id_comp is_precat.comp_id is_precat.assoc

/- We reduce the equality of precategory structures to the
   equality of the underlying category structures. -/
@[hott]
structure pc_hom_laws {C : Type _} (cat_str : category_struct C) :=
  (id_comp : ∀ {a b : C} (f : a ⟶ b), 𝟙 a ≫ f = f)
  (comp_id : ∀ {a b : C} (f : a ⟶ b), f ≫ 𝟙 b = f)
  (assoc   : ∀ {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
               (f ≫ g) ≫ h = f ≫ (g ≫ h))

@[hott, instance]
def pc_hom_laws_is_prop {C : Type _} (cat_str : category_struct C) :
  is_prop (pc_hom_laws cat_str) :=
begin 
  fapply is_prop.mk, intros hl₁ hl₂, 
  hinduction hl₁ with ic₁ ci₁ as₁, hinduction hl₂ with ic₂ ci₂ as₂, 
  fapply ap0111', 
  all_goals { exact is_prop.elim _ _ } 
end

@[hott, reducible]
def pc_str_sig (C : Type _) := 
  Σ (cat_str : category_struct C), pc_hom_laws cat_str 

@[hott, reducible]
def precat_str_eqv_sig (C : Type _) : 
    (is_precat C) ≃ (pc_str_sig C) :=
begin
  fapply equiv.mk,
  { intro pc_str,  
    exact dpair pc_str.to_category_struct (@pc_hom_laws.mk _ 
                pc_str.to_category_struct pc_str.id_comp 
                pc_str.comp_id pc_str.assoc) },
  { fapply adjointify, 
    { intro pc_str_sig, hinduction pc_str_sig with cat_str pc_hom_laws,
      exact @is_precat.mk _ cat_str pc_hom_laws.id_comp 
                        pc_hom_laws.comp_id pc_hom_laws.assoc },
    { intro pc_str_sig, hinduction pc_str_sig with cat_str pc_hom_laws,
      hsimp, hinduction pc_hom_laws, hsimp },
    { intro pc_str, hinduction pc_str with cat_str ic ci as, 
      hsimp } }
end

@[hott, reducible]
def pc_str_sig_eq_eqv_cat_str_eq {C : Type _} :
  Π (pc_str_sig₁ pc_str_sig₂ : pc_str_sig C), 
    (pc_str_sig₁ = pc_str_sig₂) ≃ ((pc_str_sig₁.1) = pc_str_sig₂.1) :=
λ pc_str_sig₁ pc_str_sig₂, subtype_eq_equiv _ _

@[hott]
def precat_str_eqv_cat_str (C : Type _) 
                           (pc_str₁ pc_str₂ : is_precat C) : 
    (pc_str₁ = pc_str₂) ≃ pc_str₁.to_category_struct =
                           pc_str₂.to_category_struct :=
eq_equiv_fn_eq_of_equiv (precat_str_eqv_sig C) pc_str₁ pc_str₂ ⬝e
pc_str_sig_eq_eqv_cat_str_eq (precat_str_eqv_sig C pc_str₁) 
                             (precat_str_eqv_sig C pc_str₂)

/- Now we bundle up precategories as a structure and show its 
   equivalence to the corresponding Σ-type. -/
@[hott]
structure Precategory :=
  (obj : Type u)
  (struct : is_precat obj)

@[hott] instance : has_coe_to_sort Precategory := 
  has_coe_to_sort.mk Type.{u} Precategory.obj

attribute [instance] Precategory.struct

@[hott]
def Precat_sig := Σ (obj : Type u), is_precat obj 

@[hott, reducible] 
def Precat_str_equiv_sig : Precategory ≃ Precat_sig :=
begin
  fapply equiv.mk,
  { exact λ C, ⟨C.obj, C.struct⟩ },
  { fapply adjointify,
    { exact λ C_sig, Precategory.mk C_sig.1 C_sig.2 },
    { intro C_sig, hsimp, rwr sigma.eta },
    { intro C, hsimp, hinduction C, hsimp } }
end

section
/- Functors are defined between precategories. But we cannot use
   `Precategory` as parameters because coercion from `Category` does
   not work.  -/   
@[hott]
structure functor (C : Type _) [is_precat C] (D : Type _) [is_precat D] :=
(obj      : C → D)
(map      : Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)))
(map_id   : ∀ (x : C), map (𝟙 x) = 𝟙 (obj x))
(map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = (map f) ≫ (map g))

infixr ` ⥤ ` :26 := functor       

attribute [hsimp] functor.map_id
attribute [hsimp] functor.map_comp

@[hott]
structure functor_ops (C : Type _) [is_precat C] (D : Type _) [is_precat D] :=
(obj      : C → D)
(map      : Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)))

@[hott]
def functor_ops_sig (C : Type _) [is_precat C] (D : Type _) [is_precat D] :=
  Σ (obj : C -> D), Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)) 

@[hott]
def functor_ops_eqv_sig (C : Type _) [is_precat C] (D : Type _) [is_precat D] :
  (functor_ops C D) ≃ (functor_ops_sig C D) :=
begin
  fapply equiv.mk,
  { intro F, exact dpair F.obj F.map },
  { fapply adjointify,
    { intro F_sig, exact functor_ops.mk F_sig.1 F_sig.2 },
    { intro F_sig, hinduction F_sig, refl },
    { intro F, hinduction F, refl } }
end  

@[hott]
def functor_to_ops {C : Type _} [is_precat C] {D : Type _} [is_precat D] :
  (functor C D) -> (functor_ops C D) :=
λ F, functor_ops.mk F.obj F.map

@[hott, reducible]
def functor_obj_ops {C : Type _} [is_precat C] {D : Type _} [is_precat D] :
  Π F, functor.obj F = (functor_ops.obj ∘ (@functor_to_ops C _ D _)) F :=
λ F, rfl

@[hott]
structure functor_laws {C : Type _} [is_precat C] {D : Type _} [is_precat D]
  (ops : functor_ops C D) :=
(map_id   : ∀ (x : C), ops.map (𝟙 x) = 𝟙 (ops.obj x))
(map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), 
              ops.map (f ≫ g) = (ops.map f) ≫ (ops.map g))

@[hott, instance]
def functor_laws_is_prop (C : Type _) [is_precat C] (D : Type _) 
  [is_precat D] (ops : functor_ops C D) : is_prop (functor_laws ops) :=
begin
  apply is_prop.mk, intros laws₁ laws₂, 
  hinduction laws₁ with map_id₁ map_comp₁, 
  hinduction laws₂ with map_id₂ map_comp₂,
  fapply ap011 functor_laws.mk, all_goals {exact is_prop.elim _ _}
end  

@[hott]
def functor_sig (C : Type _) [is_precat C] (D : Type _) [is_precat D] :=
  Σ (ops : functor_ops C D), functor_laws ops

@[hott]
def functor_eqv_sig (C : Type _) [is_precat C] (D : Type _) [is_precat D] :
  (functor C D) ≃ (functor_sig C D) :=
begin
  fapply equiv.mk,
  { intro F, exact dpair (functor_to_ops F) 
                         (functor_laws.mk F.map_id F.map_comp) },
  { fapply adjointify,
    { intro F_sig, exact functor.mk F_sig.1.obj F_sig.1.map
                                    F_sig.2.map_id F_sig.2.map_comp },
    { intro F_sig, hinduction F_sig, hsimp, fapply sigma.sigma_eq,
      { hsimp, hinduction fst, refl },
      { hsimp, hinduction fst, hinduction snd, exact idpo } },
    { intro F, hinduction F, hsimp, refl } }
end

@[hott]
def functor_eq_eqv_ops_eq {C : Type _} [is_precat C] {D : Type _} 
  [is_precat D] : Π (F G : functor C D), 
  (F = G) ≃ (functor_to_ops F = functor_to_ops G) :=
λ F G, eq_equiv_fn_eq_of_equiv (functor_eqv_sig C D) _ _ ⬝e 
       subtype_eq_equiv _ _ 

@[hott]
def functor_eq_obj_ops {C : Type _} [is_precat C] {D : Type _} 
  [is_precat D] {F G : C ⥤ D} : Π (p : F = G),
  ap functor.obj p = ap functor_ops.obj (functor_eq_eqv_ops_eq F G p) := 
begin intro p, hinduction p, rwr ap_idp end  

/- Functors are equal if their maps of objects and arrows are equal. -/
@[hott]
def functor_eq {A : Type _} [is_precat A] {B : Type _} [is_precat B] 
  {F G : A ⥤ B} : Π (p : F.obj = G.obj), 
    (F.map =[p; λ f : A -> B, Π (x y : A), (x ⟶ y) -> 
                                (f x ⟶ f y)] G.map) -> F = G :=
begin 
  intros obj_eq map_eq, apply (functor_eq_eqv_ops_eq F G)⁻¹ᶠ, 
  exact apd011 functor_ops.mk obj_eq map_eq 
end  

@[hott]
def functor_eq_idp {A : Type _} [is_precat A] {B : Type _} 
  [is_precat B] (F : A ⥤ B) : functor_eq (idpath F.obj) idpo = idp :=
begin 
  change (functor_eq_eqv_ops_eq F F)⁻¹ᶠ (apd011 functor_ops.mk 
                                       (idpath F.obj) idpo) = idp,
  have p : (functor_eq_eqv_ops_eq F F)⁻¹ᶠ (apd011 functor_ops.mk 
                                (idpath F.obj) (idpatho F.map)) =
           (functor_eq_eqv_ops_eq F F)⁻¹ᶠ idp, from rfl,
  rwr p, change _ = idpath F,
  rwr <- is_equiv.left_inv (functor_eq_eqv_ops_eq F F).to_fun 
                                                    (idpath F) 
end

@[hott]
def functor_eq_obj {A : Type _} [is_precat A] {B : Type _} [is_precat B] 
  {F G : A ⥤ B} (p : F.obj = G.obj) 
  (q : F.map =[p; λ f : A -> B, Π (x y : A), (x ⟶ y) -> 
                                (f x ⟶ f y)] G.map) : 
  ap functor.obj (functor_eq p q) = p :=
begin
  hinduction F with F_obj F_map F_mi F_mc,
  hinduction G with G_obj G_map G_mi G_mc, 
  change F_obj = G_obj at p, 
  change @F_map =[p; λ f : A -> B, Π (x y : A), (x ⟶ y) -> 
                                      (f x ⟶ f y)] @G_map at q, 
  hinduction p, hinduction q, 
  let F := functor.mk F_obj @F_map @F_mi @F_mc,
  let G := functor.mk F_obj @F_map @G_mi @G_mc,
  change ap _ ((functor_eq_eqv_ops_eq F G)⁻¹ᶠ (idpath (functor_ops.mk 
                          F_obj @F_map))) = _,
  rwr functor_eq_obj_ops, 
  rwr is_equiv.right_inv (functor_eq_eqv_ops_eq F G) 
end

@[hott, reducible]
def constant_functor {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D](d : D) : C ⥤ D := 
have id_hom_eq : ∀ d : D, 𝟙 d = 𝟙 d ≫ 𝟙 d, by intro d; hsimp,  
functor.mk (λ c : C, d) (λ c₁ c₂ f, 𝟙 d) (λ c, rfl) 
  (λ c₁ c₂ c₃ f g, (id_hom_eq d))

@[hott]
def constant_functor_map {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] (d : D) : ∀ {c₁ c₂ : C} (h : c₁ ⟶ c₂), 
  (constant_functor d).map h = 𝟙 d :=
assume c₁ c₂ h, rfl  

@[hott, reducible]
def id_functor (C : Type u) [is_precat C] : C ⥤ C :=
  functor.mk (λ c : C, c) (λ c₁ c₂ f, f) (λ c, idp) (λ c₁ c₂ c₃ f g, idp)  


@[hott]
structure nat_trans {A : Type _} [is_precat A] {B : Type _} 
  [is_precat B] (F G : A ⥤ B) :=
(app : Π c : A, (F.obj c) ⟶ (G.obj c))
(naturality : ∀ {c c' : A} (f : c ⟶ c'), 
                                 (F.map f) ≫ (app c') = (app c) ≫ (G.map f))  

infixr ` ⟹ `:10 := nat_trans

@[hott]
def is_faithful_functor {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] (F : C ⥤ D) := 
  Π {x y : C}, is_set_injective (@functor.map C _ D _ F x y) 

@[hott]
def is_fully_faithful_functor {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] (F : C ⥤ D) := 
  Π {x y : C}, is_set_bijective (@functor.map C _ D _ F x y)

@[hott, instance]
def is_fff_is_prop {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] (F : C ⥤ D) : is_prop (is_fully_faithful_functor F) :=
begin apply is_prop_dprod, intro a, apply_instance end

@[hott, reducible]
def is_fully_faithful_functor' {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] {F : C ⥤ D} : is_fully_faithful_functor F ->
  Π (x y : C), bijection (x ⟶ y) (F.obj x ⟶ F.obj y) :=
λ ff x y, bijection.mk (@functor.map C _ D _ F x y) (@ff x y) 

@[hott]
def id_functor_is_fully_faithful {C : Type u} [is_precat C] : 
  is_fully_faithful_functor (id_functor C) :=
  λ x y : C, (identity (x ⟶ y)).bij   

/- The composition of functors -/
@[hott, reducible]
def functor_comp {A₁ : Type _} [is_precat A₁] {A₂ : Type _} 
  [is_precat A₂] {A₃ : Type _} [is_precat A₃] (F : A₁ ⥤ A₂) 
  (G : A₂ ⥤ A₃) : A₁ ⥤ A₃ := 
begin
  fapply functor.mk,  
  { exact λ c : A₁, G.obj (F.obj c) }, -- map of objects
  { intros c c' f, exact G.map (F.map f) },  -- map of morphisms
  { intro x, hsimp }, -- identity morphisms are preserved
  { intros x y x f g, hsimp } --composition of morphisms is preserved
end  

infixr ` ⋙ `:25 := functor_comp 

@[hott]
def funct_id_comp {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] (F : C ⥤ D) : (id_functor C ⋙ F) = F :=
begin 
  fapply functor_eq, 
  { exact idp },
  { hsimp } 
end  

@[hott]
def funct_comp_id {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] (F : C ⥤ D) : (F ⋙ id_functor D) = F :=
begin 
  fapply functor_eq, 
  { apply eq_of_homotopy, intro c, hsimp },
  { hsimp, change F.map =[eq_of_homotopy (λ c : C, idp); 
                    λ f : C -> D, Π (x y : C), (x ⟶ y) → (f x ⟶ f y)] F.map, 
    rwr eq_of_homotopy_idp } 
end 

@[hott]
def funct_comp_assoc {C : Type _} [is_precat C] {D : Type _} 
  [is_precat D] {E : Type _} [is_precat E] {B : Type _} 
  [is_precat B] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) : 
  ((F ⋙ G) ⋙ H) = (F ⋙ (G ⋙ H)) :=
begin
  fapply functor_eq, 
  { apply eq_of_homotopy, intro c, hsimp },
  { change _ =[eq_of_homotopy (λ c : C, idp); 
                    λ f : C -> B, Π (x y : C), (x ⟶ y) → (f x ⟶ f y)] _, 
    rwr eq_of_homotopy_idp }
end  

end

/- Equalities of precategories can be characterized by 
   fully faithful functors that induce an equivalence on the types of 
   the objects. We use the Structure Identity Principle twice, on
   precategories and on category structures to deduce this 
   characterisation from univalence of the underlying types. -/
@[hott]
structure precat_iso (C D : Precategory) :=
  (functor : C ⥤ D) 
  (ff : is_fully_faithful_functor functor) 
  (equiv : is_equiv functor.obj)

@[hott]
def precat_iso_eq_of_funct_eq {C D : Precategory} {pc₁ pc₂ : precat_iso C D} : 
  (pc₁.functor = pc₂.functor) -> (pc₁ = pc₂) :=
begin
  intro funct_eq, hinduction pc₁, hinduction pc₂,
  fapply apd0111' precat_iso.mk, 
  { exact funct_eq },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

@[hott]
structure precat_iso_of_obj {C₀ C : Precategory} 
  (obj_eqv : C₀ ≃ C.obj) :=
  (hom_map      : Π {x y : C₀}, (x ⟶ y) → 
                             ((obj_eqv x) ⟶ (obj_eqv y)))
  (hom_map_id   : ∀ {x : C₀}, hom_map (𝟙 x) = 𝟙 (obj_eqv x))
  (hom_map_comp : ∀ {x y z : C₀} (f : x ⟶ y) (g : y ⟶ z), 
                   hom_map (f ≫ g) = (hom_map f) ≫ (hom_map g)) 
  (ff : Π {x y : C₀}, is_set_bijective (@hom_map x y) )   

@[hott, reducible]
def precat_iso_of_obj_equiv_iso (C₀ C : Precategory) :
  (Σ (obj_eqv : C₀ ≃ C.obj), @precat_iso_of_obj C₀ 
     (Precategory.mk C.obj C.struct) obj_eqv) ≃ precat_iso C₀ C :=
begin
  fapply equiv.mk,
  { intro pc_oi_sig, fapply precat_iso.mk,
    { exact functor.mk pc_oi_sig.1 pc_oi_sig.2.hom_map
                       pc_oi_sig.2.hom_map_id 
                       pc_oi_sig.2.hom_map_comp },
    { exact pc_oi_sig.2.ff },
    { exact pc_oi_sig.1.to_is_equiv } },
  { fapply adjointify,
    { intro pc_iso, fapply sigma.mk, 
      { exact equiv.mk pc_iso.functor.obj pc_iso.equiv },
      { exact precat_iso_of_obj.mk pc_iso.functor.map
          pc_iso.functor.map_id pc_iso.functor.map_comp pc_iso.ff } },
    { intro pc_iso, hinduction pc_iso with functor ff equiv,
      hinduction functor with obj map map_id map_comp, hsimp },
    { intro pc_oi_sig, hinduction pc_oi_sig with pc_oi pc_io, 
      hinduction pc_oi with map equiv, 
      hinduction pc_io, hsimp } }  
end

@[hott, reducible]
def cat_iso_eqv_pc_io {C : Type _} (pc_str₁ pc_str₂ : is_precat C) :
  (cat_str_sig_iso (cat_str_eqv_sig C pc_str₁.to_category_struct) 
                   (cat_str_eqv_sig C pc_str₂.to_category_struct)) ≃
  (@precat_iso_of_obj (Precategory.mk C pc_str₁) (Precategory.mk C pc_str₂)
                      (equiv.refl C)) :=
begin
  fapply equiv.mk,
  { intro css_iso, fapply precat_iso_of_obj.mk, 
    { exact λ x y, (css_iso.1 x y).map },
    { exact css_iso.2.hom_map_id },
    { exact css_iso.2.hom_map_comp },
    { exact λ x y, (css_iso.1 x y).bij } },
  { fapply adjointify,
    { intro pc_io, fapply sigma.mk, 
      { exact λ x y, bijection.mk 
                     (@precat_iso_of_obj.hom_map _ _ _ pc_io x y) 
                     (@precat_iso_of_obj.ff _ _ _ pc_io x y) },
      { exact cat_map_laws.mk pc_io.hom_map_id pc_io.hom_map_comp } },
    { intro pc_io, hsimp, hinduction pc_io, hsimp },
    { intro css_iso, hsimp, hinduction css_iso with bhm laws, 
      hsimp, fapply sigma.sigma_eq,
      { hsimp, apply eq_of_homotopy2, intros x y, hsimp, 
        rwr <- bijection.eta },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } }
end

@[hott, reducible]
def pc_str_eqv_pc_io {C : Type _} (pc_str₁ pc_str₂ : is_precat C) :
  (pc_str₁ = pc_str₂) ≃
  (@precat_iso_of_obj (Precategory.mk C pc_str₁) (Precategory.mk C pc_str₂)
                      (equiv.refl C)) :=
(precat_str_eqv_cat_str C pc_str₁ pc_str₂) ⬝e 
(cat_str_eq_eqv_iso pc_str₁.to_category_struct pc_str₂.to_category_struct) ⬝e
(cat_iso_eqv_pc_io pc_str₁ pc_str₂)                     

@[hott, reducible]
def precat_obj_ppred (C₀ : Precategory) : ppred C₀.obj :=
  ppred.mk (λ C : Type _, C₀ ≃ C) (@equiv.rfl C₀)

@[hott, reducible]
def precat_dep_ppred (C₀ : Precategory) : dep_ppred C₀.obj C₀.struct :=              
  dep_ppred.mk (precat_obj_ppred C₀) 
    (λ C pc_str_C pc_obj, @precat_iso_of_obj C₀ 
                             (Precategory.mk C pc_str_C) pc_obj) 
    (precat_iso_of_obj.mk (id_functor C₀).map (id_functor C₀).map_id
       (id_functor C₀).map_comp (@id_functor_is_fully_faithful C₀ _)) 

@[hott]
def precat_contr_ppred (C₀ : Precategory) :
  is_contr (Σ (C : Type _), (precat_dep_ppred C₀).ppred_fst.fam C) :=
begin
  fapply is_contr.mk, 
  { exact ⟨C₀.obj, @equiv.rfl C₀⟩ },
  { intro C_obj_iso, hinduction C_obj_iso with C_obj pc_oi_C,
    change _ ≃ C_obj at pc_oi_C,
    change dpair C₀.obj (@equiv.rfl C₀) = _,   
    fapply sigma.sigma_eq, 
    { exact ua pc_oi_C },
    { fapply obj_char_id_eq (eq_equiv_equiv C₀.obj) } }
end  

@[hott]
def precat_contr_dep_ppred (C₀ : Precategory) :
is_contr (Σ (pc : is_precat C₀.obj), 
  (precat_dep_ppred C₀).dep_fam C₀.obj pc 
                        (precat_dep_ppred C₀).ppred_fst.base) :=
begin
  fapply is_contr.mk, 
  { exact ⟨C₀.struct, (precat_dep_ppred _).dep_base⟩ },
  { intro pc_str_iso, hinduction pc_str_iso with pc_str pc_iso,
    hinduction C₀ with C₀_obj C₀_struct,
    change @precat_iso_of_obj (Precategory.mk C₀_obj C₀_struct) 
              (Precategory.mk C₀_obj pc_str) (equiv.refl C₀_obj) 
      at pc_iso,
    fapply sigma.sigma_eq, 
    { exact (pc_str_eqv_pc_io C₀_struct pc_str)⁻¹ᶠ pc_iso },
    { fapply obj_char_id_eq (pc_str_eqv_pc_io C₀_struct) } }
end

@[hott]
def precat_sig_equiv_obj_iso (C₀ C : Precategory) : 
  ((Precat_str_equiv_sig C₀) = (Precat_str_equiv_sig C)) ≃
  (Σ (pc_obj : C₀ ≃ C.obj), @precat_iso_of_obj C₀ 
                     (Precategory.mk C.obj C.struct) pc_obj) :=
begin
  fapply struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
                                 _ _ (Precat_str_equiv_sig C),
  { exact precat_contr_ppred C₀ },
  { exact precat_contr_dep_ppred C₀ }
end   

@[hott]
def precat_sig_equiv_obj_iso_idp (C₀ C : Precategory) : 
  (precat_sig_equiv_obj_iso C₀ C₀ idp).1 = equiv.rfl :=
begin 
  change ((struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
           (precat_contr_ppred C₀) (precat_contr_dep_ppred C₀) 
           (dpair C₀.obj _)).to_fun idp).1 = _,
  have r : (struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
           (precat_contr_ppred C₀) (precat_contr_dep_ppred C₀) 
           (dpair C₀.obj _)).to_fun idp = 
           ⟨@equiv.rfl C₀, (precat_dep_ppred C₀).dep_base⟩,
  from struct_id_char_of_contr_idp C₀.struct (precat_dep_ppred C₀)
        (precat_contr_ppred C₀) (precat_contr_dep_ppred C₀), 
  exact ap sigma.fst r
end

@[hott]
def precat_sig_equiv_obj_iso_idp_map (C₀ C : Precategory) : 
  (precat_sig_equiv_obj_iso C₀ C₀ idp).2.hom_map = 
                                          (id_functor C₀).map :=
begin 
  change ((struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
           (precat_contr_ppred C₀) (precat_contr_dep_ppred C₀) 
           (dpair C₀.obj _)).to_fun idp).2.hom_map = 
           (precat_dep_ppred C₀).dep_base.hom_map,
  apply ap precat_iso_of_obj.hom_map,
  have q : precat_sig_equiv_obj_iso_idp C₀ C₀ = idpath (@equiv.rfl C₀), from rfl,
  have s : ((struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
           (precat_contr_ppred C₀) (precat_contr_dep_ppred C₀) 
           (dpair C₀.obj _)).to_fun idp).2 =[idpath (@equiv.rfl C₀)]
           (precat_dep_ppred C₀).dep_base, by rwr <- q; rwr sigma.eq_snd,
  exact eq_of_pathover_idp s
end

@[hott]
def precat_id_equiv_iso (C D : Precategory) : 
  (C = D) ≃ (precat_iso C D) :=
(eq_equiv_fn_eq_of_equiv Precat_str_equiv_sig C D) ⬝e
(precat_sig_equiv_obj_iso C D) ⬝e
(precat_iso_of_obj_equiv_iso C D)

end precategories

end hott