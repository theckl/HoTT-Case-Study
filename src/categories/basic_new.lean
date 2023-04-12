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
@[hott]
def bij_hom_map {C : Type _} (hh₁ hh₂ : has_hom C) :=
  Π x y : C, bijection (@has_hom.hom _ hh₁ x y) 
                       (@has_hom.hom _ hh₂ x y)

@[hott, reducible]
def bij_hom_map_id {C : Type _} (hh : has_hom C) : bij_hom_map hh hh :=
  λ x y, identity (@has_hom.hom _ hh x y)  

@[hott, reducible]
def hom_ppred {C : Type} (hh₀ : has_hom C) : ppred hh₀ :=
  ppred.mk (λ hh : has_hom C, bij_hom_map hh₀ hh) 
           (bij_hom_map_id hh₀)

@[hott]
def is_contr_hom {C : Type} (hh₀ : has_hom C) :
  is_contr (Σ hh : has_hom C, bij_hom_map hh₀ hh) :=
begin 
  fapply is_contr.mk, 
  { exact ⟨hh₀, bij_hom_map_id hh₀⟩ },
  { intro hb, hinduction hb with hh bij,
    hinduction hh₀ with hom₀, hinduction hh with hom, 
    fapply sigma.sigma_eq, 
    { apply ap has_hom.mk, apply eq_of_homotopy2, intros x y, 
      exact (@set_eq_equiv_bij (hom₀ x y) (hom x y))⁻¹ᶠ (bij x y) },
    { apply pathover_of_tr_eq, apply eq_of_homotopy2, intros x y,
      apply bijection_eq_from_map_eq, sorry } }
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

/-- The structure of a precategory. -/
@[hott, class]
structure is_precat (obj : Type u) 
extends category_struct.{v} obj : Type (max u (v+1)) :=
(id_comp : ∀ {a b : obj} (f : hom a b), 𝟙 a ≫ f = f)
(comp_id : ∀ {a b : obj} (f : hom a b), f ≫ 𝟙 b = f)
(assoc   : ∀ {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d),
  (f ≫ g) ≫ h = f ≫ (g ≫ h))

attribute [hsimp] is_precat.id_comp is_precat.comp_id is_precat.assoc

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
variables (C : Precategory) (D : Precategory) (E : Precategory)

/- Functors are defined between precategories. -/
@[hott]
structure functor :=
(obj      : C → D)
(map      : Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)))
(map_id   : ∀ (x : C), map (𝟙 x) = 𝟙 (obj x))
(map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = (map f) ≫ (map g))

infixr ` ⥤ ` :26 := functor       

attribute [hsimp] functor.map_id
attribute [hsimp] functor.map_comp

@[hott]
def functor_eta (F : C ⥤ D) : 
  F = functor.mk F.obj F.map F.map_id F.map_comp :=
begin hinduction F, refl end 

@[hott]
def functor_eta_mk :
  Π obj map map_id map_comp, functor_eta C D (functor.mk obj map map_id map_comp) = idp :=
assume obj map map_id map_comp, rfl  

@[hott]
def functor_mk_obj :
  Π obj map map_id map_comp, @functor.obj C D (functor.mk obj map map_id map_comp) = obj :=
assume obj map map_id map_comp, rfl   

/- Functors are equal if their maps of objects and arrows are equal. -/
@[hott]
def functor_eq {F G : C ⥤ D} :
  Π (p : F.obj = G.obj), 
    (F.map =[p; λ f : C -> D, Π (x y : C), (x ⟶ y) -> (f x ⟶ f y)] G.map) -> F = G :=
begin 
  intros p q, 
  exact (functor_eta C D F) ⬝ (apd01111_v2 functor.mk p q 
          (pathover_of_tr_eq (is_prop.elim _ _))  (pathover_of_tr_eq (is_prop.elim _ _)))
        ⬝ (functor_eta C D G)⁻¹  
end  

@[hott]
def functor_eq_idp' {obj : C -> D} 
  (map : Π (c₁ c₂ : C), (c₁ ⟶ c₂) -> (obj c₁ ⟶ obj c₂)) :
  Π mi mc, functor_eq C D (@idp _ (functor.mk obj map mi mc).obj) idpo = idp :=
begin 
  intros mi mc,                                          
  change idp ⬝ (apd01111_v2 functor.mk idp idpo 
           (pathover_of_tr_eq (is_prop.elim _ _)) (pathover_of_tr_eq (is_prop.elim _ _))) 
         ⬝ inverse idp = _, 
  rwr idp_con, rwr idp_inv, rwr con_idp,             
  have H1 : pathover_of_tr_eq (is_prop.elim (apd011 (λ (a : C → D) 
              (b : Π {x y : C}, (x ⟶ y) → (a x ⟶ a y)), Π (x : C), b (𝟙 x) = 𝟙 (a x))
              idp idpo ▸[id] mi) mi) = idpo, by apply dep_set_eq_eq,
  have H2 : pathover_of_tr_eq (is_prop.elim (apd011 (λ (a : C → D) (b : Π {x y : C}, 
              (x ⟶ y) → (a x ⟶ a y)), Π (x y z : C) (f : x ⟶ y) (g : y ⟶ z), 
              b (f ≫ g) = b f ≫ b g) idp idpo ▸[id] @mc) @mc) = idpo,
    by apply dep_set_eq_eq,        
  rwr H1, rwr H2
end

@[hott]
def functor_eq_idp {F : C ⥤ D} :
  functor_eq C D (@idp _ F.obj) idpo = idp :=
begin hinduction F, rwr functor_eq_idp' end

@[hott]
def functor_eq_obj {F G : C ⥤ D} :
  Π (p : F.obj = G.obj) q, (ap functor.obj (functor_eq C D p q)) = p :=
begin 
  intros p q, 
  change (ap _ ((functor_eta C D F) ⬝ (apd01111_v2 functor.mk p q 
          (pathover_of_tr_eq (is_prop.elim _ _))  (pathover_of_tr_eq (is_prop.elim _ _)))
        ⬝ (functor_eta C D G)⁻¹)) = p, 
  rwr ap_con, rwr ap_con, hinduction F, hinduction G, 
  rwr functor_eta_mk, rwr functor_eta_mk, rwr idp_inv, rwr ap_idp, rwr ap_idp, rwr con_idp,
  rwr idp_con, rwr ap_apd01111_v2 _ _ _ _ _ _ (functor_mk_obj C D),  
  change idp ⬝ p ⬝ idp⁻¹ = p, rwr idp_inv, rwr con_idp, rwr idp_con  
end    

@[hott]
def functor_eq_change_path {F G : C ⥤ D} 
  {p p' : F.obj = G.obj} (q : p = p')
  (r : (F.map =[p; λ f : C -> D, Π (x y : C), (x ⟶ y) -> (f x ⟶ f y)] G.map)) :
  functor_eq C D p' (change_path q r) = functor_eq C D p r :=
begin hinduction q, rwr change_path_idp end  

@[hott]
def functor_eq_eta {F G : C ⥤ D} (p : F = G) :
  functor_eq C D (ap functor.obj p) 
                 (pathover_ap (λ f : C -> D, Π (x y : C), (x ⟶ y) -> (f x ⟶ f y)) 
                              functor.obj (apd functor.map p)) = p :=
begin 
  hinduction p, rwr apd_idp, 
  change functor_eq C D (ap functor.obj (refl F)) 
                        (change_path (ap_idp F functor.obj)⁻¹ idpo) = _, 
  rwr functor_eq_change_path, rwr functor_eq_idp
end  

@[hott, reducible]
def constant_functor (d : D) : 
  C ⥤ D := 
have id_hom_eq : ∀ d : D, 𝟙 d = 𝟙 d ≫ 𝟙 d, by intro d; hsimp,  
functor.mk (λ c : C, d) (λ c₁ c₂ f, 𝟙 d) (λ c, rfl) 
  (λ c₁ c₂ c₃ f g, (id_hom_eq d))

@[hott]
def constant_functor_map (d : D) :
  ∀ {c₁ c₂ : C} (h : c₁ ⟶ c₂), (constant_functor C D d).map h = 𝟙 d :=
assume c₁ c₂ h, rfl  

@[hott, reducible]
def id_functor : C ⥤ C :=
  functor.mk (λ c : C, c) (λ c₁ c₂ f, f) (λ c, idp) (λ c₁ c₂ c₃ f g, idp)  


@[hott]
structure nat_trans (F G : C ⥤ D) :=
(app : Π c : C, (F.obj c) ⟶ (G.obj c))
(naturality : ∀ {c c' : C} (f : c ⟶ c'), 
                                 (F.map f) ≫ (app c') = (app c) ≫ (G.map f))  

infixr ` ⟹ `:10 := nat_trans _ _

end

section
variables {B : Precategory} {C : Precategory} {D : Precategory} {E : Precategory}

@[hott]
def is_faithful_functor (F : C ⥤ D) := 
  Π {x y : C}, is_set_injective (@functor.map C D F x y) 

@[hott]
def is_fully_faithful_functor (F : C ⥤ D) := 
  Π {x y : C}, is_set_bijective (@functor.map C D F x y)

@[hott]
def id_functor_is_fully_faithful : is_fully_faithful_functor (id_functor C) :=
  λ x y : C, (identity (x ⟶ y)).bij   

/- The composition of functors -/
@[hott, reducible]
def functor_comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E := 
begin
  fapply functor.mk,  
  { exact λ c : C, G.obj (F.obj c) }, -- map of objects
  { intros c c' f, exact G.map (F.map f) },  -- map of morphisms
  { intro x, hsimp }, -- identity morphisms are preserved
  { intros x y x f g, hsimp } --composition of morphisms is preserved
end  

infixr ` ⋙ `:25 := functor_comp 

@[hott]
def funct_id_comp (F : C ⥤ D) : 
  (id_functor C ⋙ F) = F :=
begin 
  fapply functor_eq, 
  { apply eq_of_homotopy, intro c, hsimp },
  { hsimp, change F.map =[eq_of_homotopy (λ c : C, idp); 
                    λ f : C -> D, Π (x y : C), (x ⟶ y) → (f x ⟶ f y)] F.map, 
    rwr eq_of_homotopy_idp } 
end  

@[hott]
def funct_comp_id (F : C ⥤ D) : 
  (F ⋙ id_functor D) = F :=
begin 
  fapply functor_eq, 
  { apply eq_of_homotopy, intro c, hsimp },
  { hsimp, change F.map =[eq_of_homotopy (λ c : C, idp); 
                    λ f : C -> D, Π (x y : C), (x ⟶ y) → (f x ⟶ f y)] F.map, 
    rwr eq_of_homotopy_idp } 
end 

@[hott]
def funct_comp_assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B) : 
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

/- This reduces the equality of precategory structures to the
   equality of the underlying category structures. -/
@[hott]
def precat_str_eqv_cat_str (C : Type _) 
                           (pc_str₁ pc_str₂ : is_precat C) : 
    (pc_str₁ = pc_str₂) ≃ pc_str₁.to_category_struct =
                           pc_str₂.to_category_struct :=
eq_equiv_fn_eq_of_equiv (precat_str_eqv_sig C) pc_str₁ pc_str₂ ⬝e
pc_str_sig_eq_eqv_cat_str_eq (precat_str_eqv_sig C pc_str₁) 
                             (precat_str_eqv_sig C pc_str₂)

@[hott]
structure precat_iso_of_obj {C₀ C : Precategory} 
  (obj_eqv : C₀ ≃ C.obj) :=
  (hom_map      : Π {x y : C₀}, (x ⟶ y) → 
                             ((obj_eqv x) ⟶ (obj_eqv y)))
  (hom_map_id   : ∀ {x : C₀}, hom_map (𝟙 x) = 𝟙 (obj_eqv x))
  (hom_map_comp : ∀ {x y z : C₀} (f : x ⟶ y) (g : y ⟶ z), 
                   hom_map (f ≫ g) = (hom_map f) ≫ (hom_map g)) 
  (ff : Π {x y : C₀}, is_set_bijective (@hom_map x y) )

@[hott] 
structure pc_hom_ops {C : Type _} (hh : has_hom C) :=
  (id       : Π a : C, a ⟶ a)
  (comp     : Π {a b c : C}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c))

@[hott]
def cat_str_sig (C : Type _) := Σ (hh : has_hom C), pc_hom_ops hh

@[hott]
def cat_str_eqv_sig (C : Type _) : (category_struct C) ≃ (cat_str_sig C) :=
begin
  fapply equiv.mk,
  { intro cat_str, 
    exact dpair cat_str.to_has_hom (@pc_hom_ops.mk _ 
                   cat_str.to_has_hom cat_str.id cat_str.comp) },
  { fapply adjointify,
    { intro cat_str_sig, 
      exact @category_struct.mk _ cat_str_sig.1 cat_str_sig.2.id 
                                              cat_str_sig.2.comp },
    { intro cat_str_sig, hinduction cat_str_sig with hh hom_ops, 
      hinduction hom_ops with id comp, hsimp },
    { intro cat_str, hinduction cat_str with hh id comp, hsimp } }
end

@[hott, reducible]
def cat_str_dep_ppred {C : Type} (cat_str₀ : cat_str_sig C) :           
  dep_ppred cat_str₀.1 cat_str₀.2 :=
dep_ppred.mk (hom_ppred cat_str₀.1) (λ hh hh_ops bhm, sorry) sorry

@[hott]
def precat_streq_eqv_iso_obj {C₀ : Precategory} (str : is_precat C₀) :
  (C₀.struct = str) ≃ @precat_iso_of_obj C₀ 
                  (Precategory.mk C₀.obj str) (@equiv.rfl C₀) :=
sorry     

@[hott]
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
def precat_obj_ppred (C₀ : Precategory) : ppred C₀.obj :=
  ppred.mk (λ C : Type _, C₀ ≃ C) (@equiv.rfl C₀)

@[hott, reducible]
def precat_dep_ppred (C₀ : Precategory) : dep_ppred C₀.obj C₀.struct :=              
  dep_ppred.mk (precat_obj_ppred C₀) 
    (λ C pc_str_C pc_obj, @precat_iso_of_obj C₀ 
                             (Precategory.mk C pc_str_C) pc_obj) 
    (precat_iso_of_obj.mk (id_functor C₀).map (id_functor C₀).map_id
       (id_functor C₀).map_comp (@id_functor_is_fully_faithful C₀)) 

@[hott]
def precat_sig_equiv_obj_iso (C₀ C : Precategory) : 
  ((Precat_str_equiv_sig C₀) = (Precat_str_equiv_sig C)) ≃
  (Σ (pc_obj : C₀ ≃ C.obj), @precat_iso_of_obj C₀ 
                     (Precategory.mk C.obj C.struct) pc_obj) :=
begin
  fapply struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
                                 _ _ (Precat_str_equiv_sig C),
  { fapply is_contr.mk, 
    { exact ⟨C₀.obj, @equiv.rfl C₀⟩ },
    { intro C_obj_iso, hinduction C_obj_iso with C_obj pc_oi_C,
      change _ ≃ C_obj at pc_oi_C,
      change dpair C₀.obj (@equiv.rfl C₀) = _,   
      fapply sigma.sigma_eq, 
      { exact ua pc_oi_C },
      { fapply obj_char_id_eq (eq_equiv_equiv C₀.obj) } } },
  { fapply is_contr.mk, 
    { exact ⟨C₀.struct, (precat_dep_ppred _).dep_base⟩ },
    { --have p : (precat_dep_ppred C₀).ppred_fst.base = @equiv.rfl C₀, from rfl,
      intro pc_str_iso, hinduction pc_str_iso with pc_str pc_iso,
      --change precat_iso_of_obj _ at pc_iso, rwr p at pc_iso,
      fapply sigma.sigma_eq, 
      { exact (precat_streq_eqv_iso_obj pc_str)⁻¹ᶠ pc_iso },
      { fapply obj_char_id_eq (@precat_streq_eqv_iso_obj C₀) 
                              pc_str pc_iso } } }
end   

@[hott]
def precat_id_equiv_iso (C D : Precategory) : 
  (C = D) ≃ (precat_iso C D) :=
(eq_equiv_fn_eq_of_equiv Precat_str_equiv_sig C D) ⬝e
(precat_sig_equiv_obj_iso C D) ⬝e
(precat_iso_of_obj_equiv_iso C D)

end precategories


open precategories
namespace categories

/- Definition of categorical isomorphisms. -/
@[hott]
structure iso {C : Type u} [is_precat.{v} C] (a b : C) :=
  (hom : a ⟶ b)
  (inv : b ⟶ a) 
  (r_inv : inv ≫ hom = 𝟙 b) 
  (l_inv : hom ≫ inv = 𝟙 a) 

postfix `⁻¹ʰ`:std.prec.max_plus := iso.inv

infix ` ≅ `:25 := iso

@[hott]
structure is_iso {C : Precategory} {a b : C} (f : a ⟶ b) :=
  (inv : b ⟶ a)
  (r_inv : inv ≫ f = 𝟙 b)
  (l_inv : f ≫ inv = 𝟙 a)

@[hott]
def is_iso_to_iso {C : Precategory} {a b : C} (f : a ⟶ b) 
  (H : is_iso f) : a ≅ b := iso.mk f H.inv H.r_inv H.l_inv

@[hott]
def iso_to_is_iso {C : Precategory} {a b : C} (f : a ≅ b) : 
  is_iso f.hom := is_iso.mk f.inv f.r_inv f.l_inv  

@[hott]
def iso.eta {C : Precategory} {a b : C} (i : a ≅ b) : 
  i = iso.mk i.hom i.inv i.r_inv i.l_inv :=
begin hinduction i, hsimp end  

@[hott, hsimp]
def inv_iso {C : Precategory} {a b : C} (i : a ≅ b) : b ≅ a :=
  iso.mk i.inv i.hom i.l_inv i.r_inv

/- Calculation rules for isomorphisms. -/
@[hott, hsimp]
def iso_inv_inv {C : Precategory} {a b : C} (i : a ≅ b) :
  (inv_iso i)⁻¹ʰ = i.hom :=
by hsimp 

@[hott, hsimp]
def iso_rcancel {C : Precategory} {a b c : C} (i : a ≅ b)
  {g h : c ⟶ a} : g ≫ i.hom = h ≫ i.hom -> g = h :=
assume pc, 
have pc_inv : (g ≫ i.hom) ≫ i.inv = (h ≫ i.hom) ≫ i.inv, from 
  ap (λ h : c ⟶ b, h ≫ i.inv) pc,
calc   g = g ≫ 𝟙 a : by hsimp
     ... = g ≫ (i.hom ≫ i.inv) : by rwr <-i.l_inv
     ... = (g ≫ i.hom) ≫ i.inv : by hsimp
     ... = (h ≫ i.hom) ≫ i.inv : by rwr pc_inv
     ... = h ≫ (i.hom ≫ i.inv) : by hsimp
     ... = h ≫ 𝟙 a : by rwr i.l_inv     
     ... = h : by hsimp 

@[hott, hsimp]
def iso_lcancel {C : Precategory} {a b c : C} (i : a ≅ b)
  {g h : b ⟶ c} : i.hom ≫ g = i.hom ≫ h -> g = h :=
assume cp, 
have cp_inv : i.inv ≫ (i.hom ≫ g) = i.inv ≫ (i.hom ≫ h), from 
  ap (λ h : a ⟶ c, i.inv ≫ h) cp,
calc   g = 𝟙 b ≫ g : by hsimp
     ... = (i.inv ≫ i.hom) ≫ g : by rwr <-i.r_inv
     ... = i.inv ≫ (i.hom ≫ g) : by hsimp
     ... = i.inv ≫ (i.hom ≫ h) : by rwr cp_inv
     ... = (i.inv ≫ i.hom) ≫ h : by hsimp
     ... = 𝟙 b ≫ h : by rwr i.r_inv     
     ... = h : by hsimp 

@[hott, hsimp]
def iso_move_lr {C : Precategory} {a b c : C} (i : a ≅ b)
  (g : b ⟶ c) (h : a ⟶ c) : i.hom ≫ g = h -> g = i.inv ≫ h :=
assume pcr,
have i.inv ≫ i.hom ≫ g = i.inv ≫ h, from ap (λ h : a ⟶ c, i.inv ≫ h) pcr,
calc g   = 𝟙 b ≫ g : by hsimp
     ... = (i.inv ≫ i.hom) ≫ g : by rwr <-i.r_inv
     ... = i.inv ≫ (i.hom ≫ g) : by hsimp
     ... = i.inv ≫ h : by rwr pcr   

@[hott, hsimp]
def iso_move_rl {C : Precategory} {a b c : C} (i : a ≅ b)
  (g : c ⟶ a) (h : c ⟶ b) : g ≫ i.hom = h -> g = h ≫ i.inv :=
assume pcl,
have (g ≫ i.hom) ≫ i.inv = h ≫ i.inv, from ap (λ h : c ⟶ b, h ≫ i.inv) pcl,
calc g   = g ≫ 𝟙 a : by hsimp
     ... = g ≫ (i.hom ≫ i.inv) : by rwr <-i.l_inv
     ... = (g ≫ i.hom) ≫ i.inv : by hsimp
     ... = h ≫ i.inv : by rwr pcl     

/- Isomorphisms are uniquely determined by their underlying homomorphism:
   The inverse map by functorial equalities, and the functorial equalities 
   because the types of homomorphisms are sets. -/
@[hott]
def hom_eq_to_iso_eq {C : Precategory} {a b : C} {i j : a ≅ b} :
  i.hom = j.hom -> i = j :=
assume hom_eq, 
have inv_eq : i.inv = j.inv, from 
  calc i.inv = i.inv ≫ 𝟙 a : by hsimp
       ...   = i.inv ≫ (j.hom ≫ j.inv) : by rwr j.l_inv⁻¹ 
       ...   = (i.inv ≫ j.hom) ≫ j.inv : by hsimp
       ...   = (i.inv ≫ i.hom) ≫ j.inv : by rwr hom_eq⁻¹
       ...   = 𝟙 b ≫ j.inv : by rwr i.r_inv
       ...   = j.inv : by hsimp,
let R := λ (f : a ⟶ b) (g : b ⟶ a), g ≫ f = 𝟙 b,
    L := λ (f : a ⟶ b) (g : b ⟶ a), f ≫ g = 𝟙 a in
have r_inv_eq : i.r_inv =[ap011 R hom_eq inv_eq; id] j.r_inv, from 
  begin apply pathover_of_tr_eq, apply is_set.elim end,
have l_inv_eq : i.l_inv =[ap011 L hom_eq inv_eq; id] j.l_inv, from 
  begin apply pathover_of_tr_eq, apply is_set.elim end, 
calc   i = iso.mk i.hom i.inv i.r_inv i.l_inv : iso.eta i 
     ... = iso.mk j.hom j.inv j.r_inv j.l_inv : 
                                        ap0111 iso.mk hom_eq inv_eq r_inv_eq l_inv_eq
     ... = j : (iso.eta j)⁻¹

@[hott, hsimp]
def id_is_iso {C : Type u} [is_precat.{v} C] (a : C) : a ≅ a := 
  have inv_eq : 𝟙 a ≫ 𝟙 a = 𝟙 a, by hsimp,
  iso.mk (𝟙 a) (𝟙 a) inv_eq inv_eq

@[hott, hsimp]
def idtoiso {C : Type u} [is_precat.{v} C] {a b : C} : (a = b) -> (a ≅ b) :=
  begin intro eq, exact eq ▸[λ c, a ≅ c] id_is_iso a end

/- `idtoiso` is natural. -/
@[hott, hsimp]
def idtoiso_refl_eq {C : Precategory} (a : C) : idtoiso (refl a) = id_is_iso a :=
  by hsimp

@[hott]
def id_inv_iso_inv {C : Precategory} {c₁ c₂ : C} (p : c₁ = c₂) :
  idtoiso p⁻¹ = inv_iso (idtoiso p) := 
begin hinduction p, refl end 

/- The next two facts correspond to [HoTT-Book, Lem.9.1.9]. -/
@[hott]
def id_hom_tr_comp {C : Precategory} {c₁ c₂ d : C} (p : c₁ = c₂)
  (h : c₁ ⟶ d) : p ▸ h = (idtoiso p)⁻¹ʰ ≫ h :=
begin hinduction p, hsimp end   

@[hott]
def id_hom_tr_comp' {C : Precategory} {c₁ c₂ d : C} (p : c₁ = c₂)
  (h : d ⟶ c₁) : p ▸ h = h ≫ (idtoiso p).hom :=
begin hinduction p, hsimp end

/-- The structure of a category. -/
@[hott]
class is_cat (obj : Type u) extends is_precat.{v} obj :=
  (ideqviso : ∀ a b : obj, is_equiv (@idtoiso _ _ a b)) 

attribute [instance] is_cat.ideqviso

@[hott]
structure Category :=
  (obj : Type u)
  (struct : is_cat obj)
/-
@[hott, instance]
def Cat.to_obj : has_coe_to_sort Category := 
  has_coe_to_sort.mk Type.{u} Category.obj
-/
@[hott, instance]
def Cat.to_Precat : has_coe Category Precategory := 
  has_coe.mk (λ C : Category, Precategory.mk C.obj (C.struct.to_is_precat))

attribute [instance] Category.struct

@[hott, hsimp]
def category.isotoid {C : Category} : 
  Π {a b : C}, a ≅ b -> a = b :=
assume a b iso,  
@is_equiv.inv _ _ (@idtoiso C.obj _ a b) (is_cat.ideqviso a b) iso  

@[hott, hsimp]
def category.idtoiso_rinv {C : Category} {a b : C} :
  ∀ i : a ≅ b, idtoiso (idtoiso⁻¹ᶠ i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_linv {C : Category} {a b : C} :
  ∀ p : a = b, idtoiso⁻¹ᶠ (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_rinv' {C : Category} {a b : C} :
  ∀ i : a ≅ b, idtoiso (category.isotoid i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_linv' {C : Category} {a b : C} :
  ∀ p : a = b, category.isotoid (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b) 

@[hott]
def isotoid_id_refl {C : Category} :
  Π (a : C), category.isotoid (id_is_iso a) = refl a :=
begin 
  intro a, rwr <- idtoiso_refl_eq  a, 
  exact category.idtoiso_linv (refl a) 
end 

@[hott]
def iso_hom_tr_comp {C : Category} {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : c₁ ⟶ d) : (idtoiso⁻¹ᶠ i) ▸ h = i⁻¹ʰ ≫ h :=
begin 
  rwr <-(category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp (idtoiso⁻¹ᶠ i) h
end 

@[hott]
def iso_hom_tr_comp' {C : Category} {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : d ⟶ c₁) : (idtoiso⁻¹ᶠ i) ▸ h = h ≫ i.hom :=
begin 
  rwr <-(category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp' (idtoiso⁻¹ᶠ i) h
end

end categories

end hott