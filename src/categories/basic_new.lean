import sets.algebra init2 types2 sets.axioms

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc hott.is_equiv

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
   the objects. Following the proof in [HoTT-Book, Lem.9.4.15] we split 
   up equalities of precageories and isomorphisms of precategories into
   components and use univalence to show their equivalence. -/
@[hott] 
structure has_hom_eq_comp {obj : Type} (hh₁ hh₂ : has_hom obj) := 
  (pₕ : Π (a b : obj), @has_hom.hom _ hh₁ a b = @has_hom.hom _ hh₂ a b)  

@[hott, reducible]
def hh_eqtocomp {obj : Type} {hh₁ hh₂ : has_hom obj} : 
  hh₁ = hh₂ -> has_hom_eq_comp hh₁ hh₂ :=
begin
  intro p, exact has_hom_eq_comp.mk 
  (λ a b, ap (λ hh, @has_hom.hom _ hh a b) p) 
end

@[hott, reducible]
def hh_comptoeq {obj : Type} {hh₁ hh₂ : has_hom obj} :
  has_hom_eq_comp hh₁ hh₂ -> hh₁ = hh₂ :=
begin
  hinduction hh₁ with h₁, hinduction hh₂ with h₂,
  intro pc, hinduction pc, 
  exact ap has_hom.mk (eq_of_homotopy2 pₕ)
end

@[hott]
def hh_eq_rinv {obj : Type} {hh₁ hh₂ : has_hom obj} :
  Π hhc : has_hom_eq_comp hh₁ hh₂, hh_eqtocomp (hh_comptoeq hhc) = hhc :=
begin
  hinduction hh₁ with h₁, hinduction hh₂ with h₂,
  intro hhc, hinduction hhc with pₕ, 
  apply ap has_hom_eq_comp.mk, apply eq_of_homotopy2, intros a b, hsimp,
  change ap _ (ap has_hom.mk _) = _, rwr <- ap_compose, hsimp,
  rwr ap_ev_eq_of_hty2_ev
end

@[hott]
def hh_eq_linv {obj : Type} {hh₁ hh₂ : has_hom obj} :
  Π hh_eq: hh₁ = hh₂, hh_comptoeq (hh_eqtocomp hh_eq) = hh_eq :=
begin 
  intro hh_eq, hinduction hh_eq, hinduction hh₁ with h₁, 
  change ap has_hom.mk _ = ap has_hom.mk idp, rwr ap_idp, 
  change ap has_hom.mk (eq_of_homotopy2 (apd100 (@idp _ 
    (@has_hom.hom _ (has_hom.mk h₁))))) = _,
  rwr hty2_of_ap100_eq_inv
end    

@[hott, hsimp]
def cs_hom {obj : Type} :
  category_struct obj -> (obj -> obj -> Set) :=
λ cat_str : category_struct obj, @has_hom.hom _ cat_str.to_has_hom  

@[hott, hsimp]
def cs_id {obj : Type} :
  Π cs : category_struct obj, Π a : obj, cs_hom cs a a :=
λ cs : category_struct obj, λ a : obj, @category_struct.id _ cs a

@[hott, hsimp]
def cs_comp {obj : Type} :
  Π cs : category_struct obj, Π {a b c : obj} (f : cs_hom cs a b) 
                                (g : cs_hom cs b c), cs_hom cs a c :=
λ cs : category_struct obj, λ (a b c : obj) (f : cs_hom cs a b) 
          (g : cs_hom cs b c), @category_struct.comp _ cs _ _ _ f g   

@[hott] 
structure cat_str_eq_comp {obj : Type} (cat_str₁ cat_str₂ : category_struct obj) :=
  (pₕ : Π (a b : obj), (cs_hom cat_str₁) a b = (cs_hom cat_str₂) a b)
  (pᵢ : Π a : obj, ((pₕ a a) ▸ cs_id cat_str₁ a) = cs_id cat_str₂ a)
  (pc : Π {a b c : obj} (f : cs_hom cat_str₁ a b) (g : cs_hom cat_str₁ b c), 
          ((pₕ a c) ▸ (cs_comp cat_str₁ f g)) = 
                        cs_comp cat_str₂ ((pₕ a b) ▸ f) ((pₕ b c) ▸ g))

@[hott]
def cs_eqtocomp {obj : Type} (cat_str₁ cat_str₂ : category_struct obj) :
  (cat_str₁ = cat_str₂) -> cat_str_eq_comp cat_str₁ cat_str₂ :=
begin
  hinduction cat_str₁ with hh₁ id₁ comp₁, 
  hinduction cat_str₂ with hh₂ id₂ comp₂,
  intro p, 
  let ph : hh₁ = hh₂ := ap (@category_struct.to_has_hom _) p,
  let pi : id₁ =[ph; λ (hh : has_hom obj), Π (a : obj), 
                                  @has_hom.hom _ hh a a] id₂ := 
    pathover_ap (λ hh : has_hom obj, Π a : obj, @has_hom.hom _ hh a a) 
        (@category_struct.to_has_hom _) (apd (@category_struct.id _) p), 
  let pc : @comp₁ =[ph; λ (hh : has_hom obj), Π (a b c: obj)
                          (f : @has_hom.hom _ hh a b) (g : @has_hom.hom _ hh b c), 
                          @has_hom.hom _ hh a c] @comp₂ := 
    pathover_ap (λ hh : has_hom obj, Π (a b c: obj)
                  (f : @has_hom.hom _ hh a b) (g : @has_hom.hom _ hh b c), 
                  @has_hom.hom _ hh a c) 
      (@category_struct.to_has_hom _) (apd (@category_struct.comp _) p),       
  fapply cat_str_eq_comp.mk,
  { exact (hh_eqtocomp ph).pₕ },
  { hsimp, intro a, rwr tr_ap_id, rwr <- ap_compose, rwr <- tr_ap_id, 
    rwr <- @tr_fn_tr_eval _ _ (λ hh a, @has_hom.hom _ hh a a) _ _ id₁ ph a, 
    exact apd10 (tr_eq_of_pathover pi) a },
  { hsimp, intros a b c f g, 
    rwr tr_ap_id, rwr <- ap_compose, rwr <- tr_ap_id, 
    rwr tr_ap_id _ f, rwr <- ap_compose, rwr <- tr_ap_id,
    rwr tr_ap_id _ g, rwr <- ap_compose, rwr <- tr_ap_id,
    rwr @tr_fn2_tr_ev _ ((λ hh, @has_hom.hom _ hh a b)) _ _ _ _ 
                     (@comp₁ a b c) ph f g,
    exact ap100 (tr_eq_of_pathover (po_fn_ev ph c (po_fn_ev ph b 
                                           (po_fn_ev ph a pc)))) _ _ }
end  

@[hott]
def cs_comptoeq {obj : Type} (cat_str₁ cat_str₂ : category_struct obj) :
  cat_str_eq_comp cat_str₁ cat_str₂ -> (cat_str₁ = cat_str₂) :=
begin
  hinduction cat_str₁ with hh₁ id₁ comp₁, 
  hinduction cat_str₂ with hh₂ id₂ comp₂,
  intro cs_comp, hinduction cs_comp,
  fapply apd0111' (@category_struct.mk obj),
  { exact hh_comptoeq (has_hom_eq_comp.mk pₕ) },
  { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, 
    change Π a : obj, pₕ a a ▸ id₁ a = id₂ a at pᵢ, rwr <- pᵢ a, 
    rwr tr_fn_tr_eval, rwr tr_ap_id, 
    change ap ((λ A : Set, A.carrier) ∘ 
           (λ hh : has_hom obj, @has_hom.hom _ hh a a)) _ ▸ _= _,
    rwr ap_compose (λ A : Set, A.carrier) 
           (λ hh : has_hom obj, @has_hom.hom _ hh a a) _, 
    rwr <- tr_ap_id, hinduction hh₁, hinduction hh₂, rwr <- ap_compose, 
    rwr ap_ev_eq_of_hty2_ev },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c,
    apply eq_of_homotopy2, intros f' g', 
    sorry }
end

@[hott]
structure precat_eq_comp (C D : Precategory) :=
  (pₒ : C.obj = D.obj)
  (pₕ : Π (a b : C), (a ⟶ b) = ((pₒ ▸[id] a) ⟶ (pₒ ▸[id] b)))
  (pᵢ : Π a : C, (pₕ a a) ▸ 𝟙 a = 𝟙 (pₒ ▸[id] a))
  (pc : Π {a b c : C} (f : a ⟶ b) (g : b ⟶ c), 
            (pₕ a c) ▸ (f ≫ g) = ((pₕ a b) ▸ f) ≫ ((pₕ b c) ▸ g))

@[hott]
def precat_eqtocomp {C D : Precategory} : C = D -> precat_eq_comp C D :=
begin
  intro p, hinduction p, fapply precat_eq_comp.mk, 
  { exact idp },
  { intros a b, exact idp },
  { intro a, hsimp },
  { intros a b c f g, hsimp }
end

@[hott]
def precat_comptoeq {C D : Precategory} : precat_eq_comp C D -> C = D :=
begin
  hinduction C with obj_C precat_C, hinduction D with obj_D precat_D,
  intro pcc, hinduction pcc, 
  change obj_C = obj_D at pₒ, hinduction pₒ, 
  change Π a b, (a ⟶ b) = (a ⟶ b) at pₕ, 
  change Π a, _ = 𝟙 a at pᵢ,
  fapply apd011 Precategory.mk, exact idp, 
  apply pathover_of_tr_eq, change precat_C = precat_D,
  hinduction precat_C with cat_C ic_C ci_C as_C,
  hinduction precat_D with cat_D ic_D ci_D as_D,
  fapply apd01111' (@is_precat.mk obj_C),
  { hinduction cat_C with has_hom_C id_C comp_C, 
    hinduction cat_D with has_hom_D id_D comp_D,
    hinduction has_hom_C with hom_C, hinduction has_hom_D with hom_D,    
    fapply apd0111' (@category_struct.mk obj_C),
    { exact ap has_hom.mk (eq_of_homotopy2 pₕ) },
    { apply pathover_of_tr_eq, 
      change Π a : obj_C, hom_C a a at id_C,
      have q : (ap has_hom.mk (eq_of_homotopy2 pₕ)) 
        ▸[λ hh : has_hom obj_C, Π a : obj_C, (@has_hom.hom _ hh) a a] id_C =
         ((eq_of_homotopy2 pₕ) ▸[λ h : obj_C -> obj_C -> Set, Π a : obj_C, h a a] id_C),
        from @tr_ap _ _ hom_C hom_D 
                 (λ hh : has_hom obj_C, Π a : obj_C, (@has_hom.hom _ hh) a a) 
                 has_hom.mk (eq_of_homotopy2 pₕ) id_C, 
      rwr q, apply eq_of_homotopy, intro a, 
      sorry },
    { sorry } },
  all_goals { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end


@[hott]
structure precat_iso (C D : Precategory) :=
  (functor : C ⥤ D) 
  (ff : is_fully_faithful_functor functor) 
  (eqv : is_equiv functor.obj)

@[hott]
def idtoprecat_iso (C D : Precategory) : (C = D) -> (precat_iso C D) :=
begin  
  intro p, hinduction p, fapply precat_iso.mk, 
  exact id_functor C, exact @id_functor_is_fully_faithful C, 
  exact is_equiv_id C.obj      
end

@[hott]
def precat_isotoid : Π (C D : Precategory), (precat_iso C D) -> (C = D)
| (Precategory.mk obj_C struct_C) (Precategory.mk obj_D struct_D) :=
begin 
  intro pc_iso, 
  have p : obj_C = obj_D, from 
    ua (equiv.mk pc_iso.functor.obj pc_iso.eqv),
  hinduction p,
  fapply ap (Precategory.mk obj_C), 
  hinduction struct_C with struct_C id_comp_C comp_id_C assoc_C, 
  hinduction struct_D with struct_D id_comp_D comp_id_D assoc_D, 
  fapply apd01111' (@is_precat.mk obj_C), 
  { hinduction struct_C with has_hom_C id_C comp_C, 
    hinduction struct_D with has_hom_D id_D comp_D, 
    have ph : has_hom_C = has_hom_D, from 
      begin 
        hinduction has_hom_C with hom_C, 
        hinduction has_hom_D with hom_D,
        apply ap (@has_hom.mk obj_C),
        apply eq_of_homotopy2, intros a b, 
        apply bij_to_set_eq, 
        exact bijection.mk (pc_iso.functor.map) (@pc_iso.ff a b) 
      end,
    hinduction ph,
    fapply ap011 (@category_struct.mk _ has_hom_C),
    { sorry },
    { sorry } },
  all_goals { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

@[hott]
def is_eqv_idtoprecat_iso (C D : Precategory) : 
  is_equiv (idtoprecat_iso C D) :=
sorry  

@[hott]
def id_eqv_precat_iso (C D : Precategory) : (C = D) ≃ (precat_iso C D) :=
  equiv.mk (idtoprecat_iso C D) (is_eqv_idtoprecat_iso C D)      

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