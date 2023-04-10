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
  intro p, hinduction p, 
  exact has_hom_eq_comp.mk (homotopy2.refl (@has_hom.hom _ hh₁))
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
def ap_hh_eqtocomp {obj : Type} {hh₁ hh₂ : has_hom obj} 
  (pₕ : Π (a b : obj), @has_hom.hom _ hh₁ a b = 
                                           @has_hom.hom _ hh₂ a b) :
  Π {a b : obj}, ap (λ (hh : has_hom obj), @has_hom.hom _ hh a b) 
                 (hh_comptoeq (has_hom_eq_comp.mk pₕ)) = pₕ a b := 
begin 
  intros a b, hinduction hh₁ with h₁, hinduction hh₂ with h₂, 
  rwr <- ap_compose, hsimp, rwr ap_ev_eq_of_hty2_ev 
end

@[hott]
def hh_hom_eq {obj : Type} {hh₁ hh₂ : has_hom obj} 
  (pₕ : Π (a b : obj), @has_hom.hom _ hh₁ a b = 
                                           @has_hom.hom _ hh₂ a b) :
  Π {a b : obj} (f : @has_hom.hom _ hh₁ a b), 
    (hh_comptoeq (has_hom_eq_comp.mk pₕ)) ▸ f = pₕ a b ▸ f := 
begin
  intros a b f, hinduction hh₁ with h₁, hinduction hh₂ with h₂, 
  rwr tr_ap_id, rwr <- ap_compose, 
  change ap ((λ A, trunctype.carrier A) ∘ (λ h : obj -> obj -> Set, h a b)) 
            (eq_of_homotopy2 (λ a b : obj, pₕ a b)) ▸[id] f = _,
  rwr ap_compose (λ A, trunctype.carrier A) 
                                    (λ h : obj -> obj -> Set, h a b),
  rwr ap_ev_eq_of_hty2_ev (λ (a b : obj), pₕ a b), rwr <- tr_ap_id
end

@[hott]
def hh_hom_eq_inv {obj : Type} {hh₁ hh₂ : has_hom obj} 
  (pₕ : Π (a b : obj), @has_hom.hom _ hh₁ a b = 
                                           @has_hom.hom _ hh₂ a b) :
  Π {a b : obj} (f' : @has_hom.hom _ hh₂ a b), 
    (hh_comptoeq (has_hom_eq_comp.mk pₕ))⁻¹ ▸ f' = (pₕ a b)⁻¹ ▸ f' := 
begin 
  intros a b f', hinduction hh₁ with h₁, hinduction hh₂ with h₂, 
  rwr <- ap_inv, rwr tr_ap_id, rwr <- ap_compose, 
  rwr eq_of_homotopy2_inv, 
  change ap ((λ A, trunctype.carrier A) ∘ (λ h : obj -> obj -> Set, h a b)) 
            (eq_of_homotopy2 (λ a b : obj, (pₕ a b)⁻¹)) ▸[id] f' = _,
  rwr ap_compose (λ A, trunctype.carrier A) 
                                    (λ h : obj -> obj -> Set, h a b),
  rwr ap_ev_eq_of_hty2_ev (λ (a b : obj), hott.eq.inverse (pₕ a b)),
  rwr <- tr_ap_id
end 

@[hott]
def hh_eq_rinv {obj : Type} {hh₁ hh₂ : has_hom obj} :
  Π hhc : has_hom_eq_comp hh₁ hh₂, hh_eqtocomp (hh_comptoeq hhc) = hhc :=
begin
  hinduction hh₁ with h₁, hinduction hh₂ with h₂,
  intro hhc, hinduction hhc with pₕ,
  apply homotopy2.rec_idp, 
  apply ap has_hom_eq_comp.mk, apply eq_of_homotopy2, 
  intros a b, exact ap_hh_eqtocomp pₕ
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

@[hott, reducible]
def cs_eqtohom_eq {obj : Type} {cat_str₁ cat_str₂ : category_struct obj} :
  (cat_str₁ = cat_str₂) -> cat_str₁.to_has_hom = cat_str₂.to_has_hom :=
λ p, ap (@category_struct.to_has_hom _) p 

@[hott]
def cs_eqtoid_eq {obj : Type} {cat_str₁ cat_str₂ : category_struct obj} :
  Π p : cat_str₁ = cat_str₂, cat_str₁.id =[cs_eqtohom_eq p; 
                               λ (hh : has_hom obj), Π (a : obj), 
                                 @has_hom.hom _ hh a a] cat_str₂.id :=
  λ p, pathover_ap (λ hh : has_hom obj, Π a : obj, @has_hom.hom _ hh a a) 
       (@category_struct.to_has_hom _) (apd (@category_struct.id _) p)

@[hott]
def cs_eqtocomp_eq {obj : Type} {cat_str₁ cat_str₂ : category_struct obj} :
  Π p : cat_str₁ = cat_str₂, cat_str₁.comp =[cs_eqtohom_eq p; 
                          λ (hh : has_hom obj), Π (a b c : obj) 
                            (f : @has_hom.hom _ hh a b) (g : @has_hom.hom _ hh b c), 
                          @has_hom.hom _ hh a c] cat_str₂.comp :=
λ p, pathover_ap (λ hh : has_hom obj, Π (a b c: obj)
                  (f : @has_hom.hom _ hh a b) (g : @has_hom.hom _ hh b c), 
                  @has_hom.hom _ hh a c) 
      (@category_struct.to_has_hom _) (apd (@category_struct.comp _) p)

@[hott]
def cs_ideq_fntoev {obj : Type} {hh₁ hh₂ : has_hom obj} (p : hh₁ = hh₂) 
  (id₁ : Π a : obj, @has_hom.hom _ hh₁ a a) : Π a : obj, 
  (p ▸ id₁) a = ap (λ hh : has_hom obj, @has_hom.hom _ hh a a) p ▸
                                                           id₁ a :=   
begin intro a, hinduction p, refl end

@[hott] 
def cs_compeq_fntoev {obj : Type} {hh₁ hh₂ : has_hom obj} (p : hh₁ = hh₂)
  (comp₁ : Π {a b c : obj}, (@has_hom.hom _ hh₁ a b) -> 
             (@has_hom.hom _ hh₁ b c) -> (@has_hom.hom _ hh₁ a c)) :
  Π (a b c : obj) (f : @has_hom.hom _ hh₁ a b) (g : @has_hom.hom _ hh₁ b c), 
    (p ▸[λ hh, (@has_hom.hom _ hh a b) -> (@has_hom.hom _ hh b c) -> 
               (@has_hom.hom _ hh a c)] comp₁) (p ▸ f) (p ▸ g) = 
    ap (λ hh, (@has_hom.hom _ hh a c)) p ▸ comp₁ f g :=
begin intros a b c f g, hinduction p, refl end      

@[hott] 
def cs_compeq_fntoev' {obj : Type} {hh₁ hh₂ : has_hom obj} (p : hh₁ = hh₂)
  (comp₁ : Π {a b c : obj}, (@has_hom.hom _ hh₁ a b) -> 
             (@has_hom.hom _ hh₁ b c) -> (@has_hom.hom _ hh₁ a c)) :
  Π (a b c : obj) (f : @has_hom.hom _ hh₂ a b) (g : @has_hom.hom _ hh₂ b c), 
    (p ▸[λ hh, Π a b c, (@has_hom.hom _ hh a b) -> (@has_hom.hom _ hh b c) -> 
               (@has_hom.hom _ hh a c)] @comp₁) a b c f g = 
    ap (λ hh, (@has_hom.hom _ hh a c)) p ▸ comp₁ (p⁻¹ ▸ f) (p⁻¹ ▸ g) :=
begin intros a b c f g, hinduction p, refl end 

@[hott]
def cs_hom_eq {obj : Type} {hh₁ hh₂ : has_hom obj} (p : hh₁ = hh₂) :
  Π (a b : obj) (f : @has_hom.hom _ hh₁ a b), 
    ap (λ hh, (@has_hom.hom _ hh a b)) p ▸ f = p ▸ f :=
begin 
  intros a b f, rwr tr_ap_id, rwr <- ap_compose, rwr <- tr_ap_id 
end

@[hott]
def cs_eqtocomp {obj : Type} {cat_str₁ cat_str₂ : category_struct obj} :
  (cat_str₁ = cat_str₂) -> cat_str_eq_comp cat_str₁ cat_str₂ :=
begin
  hinduction cat_str₁ with hh₁ id₁ comp₁, 
  hinduction cat_str₂ with hh₂ id₂ comp₂,
  intro p,        
  fapply cat_str_eq_comp.mk,
  { exact (hh_eqtocomp (cs_eqtohom_eq p)).pₕ },
  { hsimp, intro a, rwr <- cs_ideq_fntoev (cs_eqtohom_eq p) id₁ a,  
    exact apd10 (tr_eq_of_pathover (cs_eqtoid_eq p)) a },
  { hsimp, intros a b c f g, 
    rwr <- cs_compeq_fntoev (cs_eqtohom_eq p) @comp₁ a b c f g,
    rwr cs_hom_eq, rwr cs_hom_eq,
    apply ap100, apply tr_eq_of_pathover, 
    exact po_fn_ev (cs_eqtohom_eq p) c (po_fn_ev (cs_eqtohom_eq p) b 
          (po_fn_ev (cs_eqtohom_eq p) a (cs_eqtocomp_eq p))) }
end  

@[hott]
def cs_comptoeq {obj : Type} {cat_str₁ cat_str₂ : category_struct obj} :
  cat_str_eq_comp cat_str₁ cat_str₂ -> (cat_str₁ = cat_str₂) :=
begin
  hinduction cat_str₁ with hh₁ id₁ comp₁, 
  hinduction cat_str₂ with hh₂ id₂ comp₂,
  intro cs_comp, hinduction cs_comp,
  change Π a : obj, pₕ a a ▸ id₁ a = id₂ a at pᵢ,
  change Π (a b c : obj) f g, pₕ a c ▸ comp₁ f g = 
                                   comp₂ (pₕ a b ▸f) (pₕ b c ▸g) at pc, 
  fapply apd0111' (@category_struct.mk obj),
  { exact hh_comptoeq (has_hom_eq_comp.mk pₕ) },
  { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, 
    rwr cs_ideq_fntoev, rwr ap_hh_eqtocomp, rwr <- pᵢ a },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros a b c,
    apply eq_of_homotopy2, intros f' g',
    rwr cs_compeq_fntoev', rwr hh_hom_eq_inv, rwr hh_hom_eq_inv, 
    rwr <- cs_compeq_fntoev _ @comp₁, rwr tr_fn2_eval_tr,         
    rwr inv_tr_tr, rwr inv_tr_tr, rwr hh_hom_eq, rwr pc,
    rwr tr_inv_tr, rwr tr_inv_tr }
end

def cscomp_to_hheq {obj : Type _} {cs₁ cs₂ : category_struct obj} : 
  Π csc : cat_str_eq_comp cs₁ cs₂, 
    cs_eqtohom_eq (cs_comptoeq csc) =
    hh_comptoeq (has_hom_eq_comp.mk csc.pₕ) :=
begin 
  hinduction cs₁ with hh₁ id₁ comp₁, 
  hinduction cs₂ with hh₂ id₂ comp₂,
  intro csc, hinduction csc,
  change ap _ (apd0111' (@category_struct.mk obj) _ _ _) = _,
  let HP : Π hh id comp, @category_struct.to_has_hom obj 
    (@category_struct.mk _ hh id comp) = hh := λ hh id comp, idp,  
  rwr ap_apd0111' _ _ _ _ (@category_struct.to_has_hom obj) HP, 
  rwr idp_con
end  

@[hott]
def cs_eq_rinv {obj : Type _} {cs₁ cs₂ : category_struct obj} :
  Π csc : cat_str_eq_comp cs₁ cs₂, cs_eqtocomp (cs_comptoeq csc) = csc :=
begin
  intro csc, hinduction csc with pₕ pᵢ pc, 
  hinduction cs₁ with hh₁ id₁ comp₁, hinduction cs₂ with hh₂ id₂ comp₂,
  hinduction hh₁ with h₁, hinduction hh₂ with h₂,  
  change Π a : obj, pₕ a a ▸ id₁ a = id₂ a at pᵢ,
  change Π (a b c : obj) f g, pₕ a c ▸ comp₁ f g = 
                                comp₂ (pₕ a b ▸ f) (pₕ b c ▸ g) at pc,
  --change cat_str_eq_comp.mk _ _ _ = _,
  --fapply apd0111' cat_str_eq_comp.mk, 
  --{ rwr cscomp_to_hheq, rwr hh_eq_rinv },
  --{ rwr idp_inv, rwr cast_def, rwr idp_tr, 
    --rwr cscomp_to_hheq, 
    --sorry },
  --{ sorry }
  sorry
end 

@[hott]
def cs_eq_linv {obj : Type _} {cs₁ cs₂ : category_struct obj} :
  Π ceq : cs₁ = cs₂, cs_comptoeq (cs_eqtocomp ceq) = ceq :=
begin
  intro ceq, hinduction ceq, sorry
end

@[hott]
def is_precat_eq_comp {obj : Type _} 
  (precat₁ precat₂ : is_precat obj) :=
  cat_str_eq_comp (precat₁.to_category_struct) 
                          (precat₂.to_category_struct)

@[hott]
def is_precat_eqtocomp {obj : Type _} {precat₁ precat₂ : is_precat obj} : 
  precat₁ = precat₂ -> is_precat_eq_comp precat₁ precat₂ :=
λ p, cs_eqtocomp (ap (@is_precat.to_category_struct obj) p)

@[hott]
def is_precat_comptoeq {obj : Type _} {precat₁ precat₂ : is_precat obj} : 
  is_precat_eq_comp precat₁ precat₂ -> precat₁ = precat₂ :=
begin
   intro pc_comp, 
   hinduction precat₁ with cat₁ ic₁ ci₁ as₁,
   hinduction precat₂ with cat₂ ic₂ ci₂ as₂,
   fapply apd01111' (@is_precat.mk obj),   
   { exact cs_comptoeq pc_comp },
   all_goals { apply pathover_of_tr_eq, exact is_prop.elim _ _ }  
end

@[hott]
def is_precat_eq_rinv {obj : Type _} (precat₁ precat₂ : is_precat obj) :
  Π (pc_comp : is_precat_eq_comp precat₁ precat₂), 
    is_precat_eqtocomp (is_precat_comptoeq pc_comp) = pc_comp :=
begin
  intro pc_comp,
  hinduction precat₁ with cat₁ ic₁ ci₁ as₁,
  hinduction precat₂ with cat₂ ic₂ ci₂ as₂,
  change cs_eqtocomp (ap _ (apd01111' (@is_precat.mk obj) _ _ _ _)) = _,
  let HP : Π cs ic ci as, @is_precat.to_category_struct obj 
        (@is_precat.mk _ cs ic ci as) = cs := λ cs ic ci as, idp,
  rwr ap_apd01111' _ _ _ _ _ _ HP, rwr idp_con, rwr idp_inv, rwr con_idp,
  rwr cs_eq_rinv
end

@[hott]
structure precat_eq_comp (C D : Precategory) :=
  (pₒ : C.obj = D.obj)
  (pc_p : is_precat_eq_comp (pₒ ▸ C.struct) D.struct)

@[hott]
def precat_eqtocomp {C D : Precategory} : C = D -> precat_eq_comp C D :=
begin
  intro p, fapply precat_eq_comp.mk, 
  { exact ap Precategory.obj p },
  { apply is_precat_eqtocomp, apply tr_eq_of_pathover, 
    apply pathover_ap, exact apd Precategory.struct p }
end

@[hott]
def precat_comptoeq {C D : Precategory} : precat_eq_comp C D -> C = D :=
begin
  hinduction C with obj_C precat_C, hinduction D with obj_D precat_D,
  intro pcc, hinduction pcc,
  change obj_C = obj_D at pₒ, hinduction pₒ, hsimp at pc_p,
  apply apd011 Precategory.mk idp, 
  exact pathover_idp_of_eq _ (is_precat_comptoeq pc_p)
end

@[hott]
def precat_eq_rinv {C D : Precategory} : Π pcc : precat_eq_comp C D, 
  precat_eqtocomp (precat_comptoeq pcc) = pcc :=
begin
  hinduction C with obj_C precat_C, hinduction D with obj_D precat_D,
  intro pcc, hinduction pcc,
  change obj_C = obj_D at pₒ, hinduction pₒ, 
  change is_precat_eq_comp precat_C precat_D at pc_p, 
  change precat_eq_comp.mk _ _ = _, fapply apd011 precat_eq_comp.mk,  
  { exact ap_apd011 Precategory.mk _ _ Precategory.obj (λ obj pc, idp) },
  { sorry }
end

@[hott]
structure precat_iso (C D : Precategory) :=
  (functor : C ⥤ D) 
  (ff : is_fully_faithful_functor functor) 
  (equiv : is_equiv functor.obj)

@[hott]
def precat_isotoid : Π (C D : Precategory), (precat_iso C D) -> (C = D)
| (Precategory.mk obj_C struct_C) (Precategory.mk obj_D struct_D) :=
begin 
  intro pc_iso, 
  have p : obj_C = obj_D, from 
    ua (equiv.mk pc_iso.functor.obj pc_iso.equiv),
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
structure precat_obj_iso (C₀ : Precategory) (C : Type _) :=
  (map : C₀.obj -> C)
  (equiv : is_equiv map)

@[hott]
structure precat_iso_of_obj {C₀ C : Precategory} 
  (pc_obj : precat_obj_iso C₀ C.obj) :=
  (hom_map      : Π {x y : C₀}, (x ⟶ y) → 
                             ((pc_obj.map x) ⟶ (pc_obj.map y)))
  (hom_map_id   : ∀ (x : C₀), hom_map (𝟙 x) = 𝟙 (pc_obj.map x))
  (hom_map_comp : ∀ {x y z : C₀} (f : x ⟶ y) (g : y ⟶ z), 
                   hom_map (f ≫ g) = (hom_map f) ≫ (hom_map g))
  (ff : is_fully_faithful_functor (functor.mk pc_obj.map @hom_map
                                      hom_map_id @hom_map_comp)) 

@[hott]
def precat_iso_of_obj_equiv_iso (C₀ C : Precategory) :
  (Σ (pc_obj : precat_obj_iso C₀ C.obj), @precat_iso_of_obj C₀ 
     (Precategory.mk C.obj C.struct) pc_obj) ≃ precat_iso C₀ C :=
begin
  fapply equiv.mk,
  { intro pc_oi_sig, fapply precat_iso.mk,
    { exact functor.mk pc_oi_sig.1.map pc_oi_sig.2.hom_map
                       pc_oi_sig.2.hom_map_id 
                       pc_oi_sig.2.hom_map_comp },
    { exact pc_oi_sig.2.ff },
    { exact pc_oi_sig.1.equiv } },
  { fapply adjointify,
    { intro pc_iso, fapply sigma.mk, 
      { exact precat_obj_iso.mk pc_iso.functor.obj pc_iso.equiv },
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
  ppred.mk (λ C : Type _, precat_obj_iso C₀ C) 
           (precat_obj_iso.mk (@id C₀.obj) (is_equiv_id C₀.obj))

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
  (Σ (pc_obj : precat_obj_iso C₀ C.obj), @precat_iso_of_obj C₀ 
                     (Precategory.mk C.obj C.struct) pc_obj) :=
begin
  fapply struct_id_char_of_contr C₀.struct (precat_dep_ppred C₀)
                                 _ _ (Precat_str_equiv_sig C),
  { fapply is_contr.mk, 
    { exact ⟨C₀.obj, (precat_dep_ppred _).ppred_fst.base⟩ },
    { intro C_obj_iso, hinduction C_obj_iso with C_obj pc_oi_C,
      change precat_obj_iso _ C_obj at pc_oi_C,
      hinduction pc_oi_C with map is_equiv,
      change dpair C₀.obj (precat_obj_iso.mk (@id C₀.obj) 
                                     (is_equiv_id C₀.obj)) = _, 
      let p : C₀.obj = C_obj := ua (equiv.mk map is_equiv),  
      have q : map = (equiv_of_eq p), by rwr equiv_of_eq_ua, 
      fapply sigma.sigma_eq, 
      { exact p },
      { apply pathover_of_tr_eq, fapply apd0111'', sorry } } },
  { sorry }
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