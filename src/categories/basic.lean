import sets.setalgebra init2 sets.set_axioms

universes v v' v'' u u' u'' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc hott.is_equiv

/-
We introduce precategories and categories following the HoTT book, 
Sec. 9.1. HoTT precategories have sets of homomorphisms, and HoTT categories 
prescribe univalence : Isomorphisms are equivalent to identities of objects.

As far as possible we copy the mathlib-code in [category_theory.category.default]. In particular,
we keep the distinction of universe levels for objects and morphisms of a category.
-/

namespace categories

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
structure precategory (obj : Type u) 
extends category_struct.{v} obj : Type (max u (v+1)) :=
(id_comp : ∀ {a b : obj} (f : hom a b), 𝟙 a ≫ f = f)
(comp_id : ∀ {a b : obj} (f : hom a b), f ≫ 𝟙 b = f)
(assoc   : ∀ {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d),
  (f ≫ g) ≫ h = f ≫ (g ≫ h))

attribute [hsimp] precategory.id_comp precategory.comp_id precategory.assoc

/- Defintion of categorical isomorphisms. -/
@[hott]
structure iso {C : Type u} [precategory.{v} C] (a b : C) :=
  (hom : a ⟶ b)
  (inv : b ⟶ a) 
  (r_inv : inv ≫ hom = 𝟙 b) 
  (l_inv : hom ≫ inv = 𝟙 a) 

postfix `⁻¹ʰ`:std.prec.max_plus := iso.inv

infix ` ≅ `:25 := iso
 
@[hott]
def iso.eta {C : Type u} [precategory.{v} C] {a b : C} (i : a ≅ b) : 
  i = iso.mk i.hom i.inv i.r_inv i.l_inv :=
begin hinduction i, hsimp end  

@[hott, hsimp]
def inv_iso {C : Type u} [precategory.{v} C] {a b : C} (i : a ≅ b) : b ≅ a :=
  iso.mk i.inv i.hom i.l_inv i.r_inv

/- Calculation rules for isomorphisms. -/
@[hott, hsimp]
def iso_inv_inv {C : Type u} [precategory.{v} C] {a b : C} (i : a ≅ b) :
  (inv_iso i)⁻¹ʰ = i.hom :=
by hsimp 

@[hott, hsimp]
def iso_rcancel {C : Type u} [precategory.{v} C] {a b c : C} (i : a ≅ b)
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
def iso_lcancel {C : Type u} [precategory.{v} C] {a b c : C} (i : a ≅ b)
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
def iso_move_lr {C : Type u} [precategory.{v} C] {a b c : C} (i : a ≅ b)
  (g : b ⟶ c) (h : a ⟶ c) : i.hom ≫ g = h -> g = i.inv ≫ h :=
assume pcr,
have i.inv ≫ i.hom ≫ g = i.inv ≫ h, from ap (λ h : a ⟶ c, i.inv ≫ h) pcr,
calc g   = 𝟙 b ≫ g : by hsimp
     ... = (i.inv ≫ i.hom) ≫ g : by rwr <-i.r_inv
     ... = i.inv ≫ (i.hom ≫ g) : by hsimp
     ... = i.inv ≫ h : by rwr pcr   

@[hott, hsimp]
def iso_move_rl {C : Type u} [precategory.{v} C] {a b c : C} (i : a ≅ b)
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
def hom_eq_to_iso_eq {C : Type u} [precategory.{v} C] {a b : C} {i j : a ≅ b} :
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
def id_is_iso {C : Type u} [precategory.{v} C] (a : C) : a ≅ a := 
  have inv_eq : 𝟙 a ≫ 𝟙 a = 𝟙 a, from precategory.id_comp (𝟙 a),
  iso.mk (𝟙 a) (𝟙 a) inv_eq inv_eq

@[hott, hsimp]
def idtoiso {C : Type u} [precategory.{v} C] {a b : C} : (a = b) -> (a ≅ b) :=
  begin intro eq, hinduction eq, exact id_is_iso a end

/- `idtoiso` is natural. -/
@[hott, hsimp]
def idtoiso_refl_eq {C : Type u} [precategory.{v} C] (a : C) : idtoiso (refl a) = id_is_iso a :=
  by hsimp

@[hott]
def id_inv_iso_inv {C : Type u} [precategory.{v} C] {c₁ c₂ : C} (p : c₁ = c₂) :
  idtoiso p⁻¹ = inv_iso (idtoiso p) := 
begin hinduction p, refl end 

@[hott]
def id_hom_tr_comp {C : Type u} [precategory.{v} C] {c₁ c₂ d : C} (p : c₁ = c₂)
  (h : c₁ ⟶ d) : p ▸ h = (idtoiso p)⁻¹ʰ ≫ h :=
begin hinduction p, hsimp end   

@[hott]
def id_hom_tr_comp' {C : Type u} [precategory.{v} C] {c₁ c₂ d : C} (p : c₁ = c₂)
  (h : d ⟶ c₁) : p ▸ h = h ≫ (idtoiso p).hom :=
begin hinduction p, hsimp end 

/-- The structure of a category. -/
@[hott]
class category (obj : Type u) extends precategory.{v} obj :=
(ideqviso : ∀ a b : obj, is_equiv (@idtoiso _ _ a b)) 

attribute [instance] category.ideqviso

@[hott, hsimp]
def category.isotoid {obj : Type u} [category.{v} obj] : 
  Π {a b : obj}, a ≅ b -> a = b :=
assume a b iso,  
@is_equiv.inv _ _ _ (category.ideqviso a b) iso  

@[hott, hsimp]
def category.idtoiso_rinv {obj : Type u} [category.{v} obj] {a b : obj} :
  ∀ i : a ≅ b, idtoiso (idtoiso⁻¹ᶠ i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_linv {obj : Type u} [category.{v} obj] {a b : obj} :
  ∀ p : a = b, idtoiso⁻¹ᶠ (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b) 

@[hott]
def isotoid_id_refl {obj : Type u} [category.{v} obj] :
  Π {a : obj}, category.isotoid (id_is_iso a) = refl a :=
begin intro a, rwr <- idtoiso_refl_eq a, exact category.idtoiso_linv (refl a) end 

@[hott]
def iso_hom_tr_comp {C : Type u} [category.{v} C] {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : c₁ ⟶ d) : (idtoiso⁻¹ᶠ i) ▸ h = i⁻¹ʰ ≫ h :=
begin 
  rwr <-(category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp (idtoiso⁻¹ᶠ i) h
end 

@[hott]
def iso_hom_tr_comp' {C : Type u} [category.{v} C] {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : d ⟶ c₁) : (idtoiso⁻¹ᶠ i) ▸ h = h ≫ i.hom :=
begin 
  rwr <-(category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp' (idtoiso⁻¹ᶠ i) h
end 

section
variables (C : Type u) (D : Type u') (E : Type u'')

/- Functors are defined between precategories. -/
@[hott]
structure functor [precategory.{v} C] [precategory.{v'} D] :
  Type (max v v' u u') :=
(obj      : C → D)
(map      : Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)))
(map_id   : ∀ (x : C), map (𝟙 x) = 𝟙 (obj x))
(map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = (map f) ≫ (map g))

infixr ` ⥤ ` :26 := functor       

attribute [hsimp] functor.map_id
attribute [hsimp] functor.map_comp

@[hott]
def is_faithful_functor [precategory.{v} C] [precategory.{v'} D] (F : C ⥤ D) := 
  Π {x y : C}, is_set_injective (@functor.map C D _ _ F x y) 

@[hott, reducible]
def constant_functor [precategory.{v} C] [precategory.{v'} D] (d : D) : 
  C ⥤ D := 
have id_hom_eq : ∀ d : D, 𝟙 d = 𝟙 d ≫ 𝟙 d, by intro d; hsimp,  
functor.mk (λ c : C, d) (λ c₁ c₂ f, 𝟙 d) (λ c, rfl) 
  (λ c₁ c₂ c₃ f g, (id_hom_eq d))


@[hott]
def constant_functor_map [precategory.{v} C] [precategory.{v'} D] (d : D) :
  ∀ {c₁ c₂ : C} (h : c₁ ⟶ c₂), (constant_functor C D d).map h = 𝟙 d :=
assume c₁ c₂ h, rfl   


@[hott]
structure nat_trans [precategory.{v} C] [precategory.{v'} D] (F G : C ⥤ D) :=
(app : Π c : C, (F.obj c) ⟶ (G.obj c))
(naturality : ∀ {c c' : C} (f : c ⟶ c'), 
                                 (F.map f) ≫ (app c') = (app c) ≫ (G.map f))  

infixr ` ⟹ `:10 := nat_trans _ _

end

section
variables {C : Type u} {D : Type u'} {E : Type u''}

/- The composition of functors -/
@[hott]
def functor_comp [precategory.{v} C] [precategory.{v'} D] [precategory.{v''} E]
  (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E := 
begin
  fapply functor.mk,  
  { exact λ c : C, G.obj (F.obj c) }, -- map of objects
  { intros c c' f, exact G.map (F.map f) },  -- map of morphisms
  { intro x, hsimp }, -- identity morphisms are preserved
  { intros x y x f g, hsimp } --composition of morphisms is preserved
end  

infixr ` ⋙ `:25 := functor_comp 

end

/- We now define structures on categories and prove the Structure Identity Principle, following
   the [HoTT-Book], Section 9.8.  -/
@[hott]
structure std_structure_on (C : Type u) [category.{v} C] :=
  (P : C -> Type w)
  (H : Π {x y : C} (α : P x) (β : P y) (f : x ⟶ y), trunctype.{0} -1)
  (id_H : ∀ {x : C} (α : P x), H α α (𝟙 x))
  (comp_H : ∀ {x y z : C} (α : P x) (β : P y) (γ : P z) (f : x ⟶ y) (g : y ⟶ z), 
              H α β f -> H β γ g -> H α γ (f ≫ g))
  (std : ∀ {x : C} (α β : P x), (H α β (𝟙 x) × H β α (𝟙 x)) ≃ α = β)           

@[hott]
structure std_structure {C : Type u} [category.{v} C] (std_str : std_structure_on C) :=
  (carrier : C)
  (str : std_str.P carrier)  

@[hott]
instance {C : Type u} [category.{v} C] (std_str : std_structure_on C) : 
  has_coe (std_structure std_str) C :=
⟨λ x : std_structure std_str, x.carrier⟩  

@[hott]
def std_str_eta {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  (x : std_structure std_str) : x = std_structure.mk x.carrier x.str :=
begin hinduction x, refl end  

@[hott, instance]
def std_str_is_set {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  ∀ a : C, is_set (std_str.P a) :=
assume a, 
have eq_eq : ∀ (α β : std_str.P a), is_prop (α = β), from 
  assume α β, is_trunc_equiv_closed -1 (std_str.std α β) (prod.is_trunc_prod _ _ -1),
is_trunc_succ_intro eq_eq 

@[hott, instance]
def std_str_po_is_prop {C : Type u} [category.{v} C] (std_str : std_structure_on C)
  {a b : C} {α : std_str.P a} {β : std_str.P b} :
  ∀ p : a = b, is_prop (α =[p] β) :=
begin 
  intro p, hinduction p, 
  apply is_trunc_equiv_closed_rev -1 (pathover_idp _ α β), 
  exact is_prop.mk (@is_set.elim _ _ α β)
end   

/- Equalities like these should be produced automatically. -/
@[hott]
def ap_apd011_str {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {a b : C} {α : std_str.P a} {β : std_str.P b} : ∀ (p : a = b) (q : α =[p] β), 
                     ap std_structure.carrier (apd011 std_structure.mk p q) = p :=
begin intros p q, hinduction p, hinduction q, refl end 

@[hott]
def apd011_ap_str {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {x y : std_structure std_str} : ∀ p : x = y, 
  apd011 std_structure.mk (ap std_structure.carrier p)
         (pathover_ap std_str.P std_structure.carrier (apd std_structure.str p)) = 
  (std_str_eta x)⁻¹ ⬝ p ⬝ (std_str_eta y) :=
begin intro p, hinduction p, hinduction x, refl end  

/- As a first step, we need to construct the structure of a precategory on the standard 
   structures. -/
@[hott, instance]
def std_str_has_hom {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  has_hom (std_structure std_str) := 
has_hom.mk (λ (x y : std_structure std_str), 
            pred_Set {f ∈ (x.carrier ⟶ y) | std_str.H (x.str) (y.str) f})

@[hott]
instance hom_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {x y : std_structure std_str} : has_coe ↥(x ⟶ y) ↥(x.carrier ⟶ y.carrier) :=
⟨λ f : x ⟶ y, 
   pred_Set_map {f ∈ (x.carrier ⟶ y) | std_str.H (x.str) (y.str) f} f⟩  

@[hott]
def hom_H {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {x y : std_structure std_str} :
  Π f : x ⟶ y, std_str.H x.str y.str (↑f) :=
begin intro f, exact f.2 end              

@[hott]
def hom_eq_C_std {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {x y : std_structure std_str} (f g : x ⟶ y) : 
  (f.1 = (g.1 : x.carrier ⟶ y.carrier)) -> (f = g) :=
assume (hom_eq_C : f.1 = g.1), 
have H_eq : f.2 =[hom_eq_C; λ f : x.carrier ⟶ y, std_str.H x.str y.str f] g.2, from 
  pathover_prop_eq (λ f : x.carrier ⟶ y, std_str.H x.str y.str f) hom_eq_C (hom_H f) 
                                                                            (hom_H g),
calc f = ⟨f.1, f.2⟩ : (sigma.eta f)⁻¹ 
   ... = ⟨g.1, g.2⟩ : dpair_eq_dpair hom_eq_C H_eq
   ... = g : sigma.eta g 

@[hott, instance]
def std_str_cat_struct {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  category_struct (std_structure std_str) :=
category_struct.mk (λ x : std_structure std_str, 
                                         ⟨𝟙 ↑x, std_str.id_H x.str⟩) 
  (λ (x y z : std_structure std_str) (f : x ⟶ y) (g : y ⟶ z), 
     ⟨↑f ≫ ↑g, std_str.comp_H x.str y.str z.str ↑f ↑g (hom_H f) (hom_H g)⟩) 

@[hott]
def idhom_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  (x : std_structure std_str) : ↑(𝟙 x) = 𝟙 x.carrier :=
rfl  

@[hott]
def comp_hom_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {x y z : std_structure std_str} (f : x ⟶ y) (g : y ⟶ z) : 
  (f ≫ g).1 = (f.1 : x.carrier ⟶ y.carrier) ≫ (g.1 : y.carrier ⟶ z.carrier) :=
rfl  

@[hott, instance]
def std_str_precategory {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  precategory (std_structure std_str) :=
have ic : ∀ (x y : std_structure std_str) (f : x ⟶ y), 𝟙 x ≫ f = f, from 
  begin intros x y f, apply hom_eq_C_std _ _, rwr comp_hom_std_C, hsimp end,
have ci : ∀ (x y : std_structure std_str) (f : x ⟶ y), f ≫ 𝟙 y = f, from 
  begin intros x y f, apply hom_eq_C_std _ _, rwr comp_hom_std_C, hsimp end,
have as : ∀ (x y z w: std_structure std_str) (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ w),
          (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
  begin intros x y z w f g h, apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, hsimp end,
precategory.mk ic ci as 

/- We prove the Structure Identity principle by splitting up the equivalence making the 
   precategory into a category into 5 equivalence and by showing that the composition of the
   5 equivalence maps is `idtoiso`. 

   The first equivalence introduces the structure components in standard structures equalities. -/
@[hott]
def std_str_comp_eq {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {x y : std_structure std_str} :
  (x = y) ≃ (std_structure.mk x.carrier x.str = std_structure.mk y.carrier y.str) :=
begin hinduction x with a α, hinduction y with b β, exact equiv.rfl end

/- The second equivalence is the eta principle for standard structures equalities. -/
@[hott]
def std_str_eq_eta {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {a b : C} {α : std_str.P a} {β : std_str.P b} :
  (std_structure.mk a α = std_structure.mk b β) ≃ Σ (p : a = b), α =[p] β :=
let x := std_structure.mk a α, y := std_structure.mk b β,
    f := λ p : x = y, @dpair (a = b) (λ p : a = b, α =[p] β) 
         (ap std_structure.carrier p : a = b) 
         (pathover_ap std_str.P std_structure.carrier (apd std_structure.str p)),
    g := λ pq : Σ (p : a = b), α =[p] β, apd011 std_structure.mk pq.1 pq.2 in                         
have rinv : ∀ pq : Σ (p : a = b), α =[p] β, f (g pq) = pq, from 
  assume pq,
  have pq_1 : (f (g pq)).1 = pq.1, from 
    calc (f (g pq)).1 = ap std_structure.carrier (apd011 std_structure.mk pq.1 pq.2) : rfl
         ... = pq.1 : ap_apd011_str pq.1 pq.2,
  have pq_2 : (f (g pq)).2 =[pq_1; λ p : a = b, α =[p] β] pq.2, from po_proofs pq_1 _ _,
  calc f (g pq) = ⟨(f (g pq)).1, (f (g pq)).2⟩ : sigma.eta (f (g pq))
       ... = ⟨pq.1, pq.2⟩ : apd011 sigma.mk pq_1 pq_2
       ... = pq : sigma.eta pq,
have linv : ∀ p : x = y, g (f p) = p, from 
  assume p,
  have qx : std_str_eta x = idp, from rfl,
  calc g (f p) = apd011 std_structure.mk (ap std_structure.carrier p) (f p).2 : rfl
       ... = (std_str_eta x)⁻¹ ⬝ p ⬝ (std_str_eta y) : apd011_ap_str p
       ... = p : by rwr qx; rwr idp_inv; rwr idp_con p; rwr con_idp p,
equiv.mk f (adjointify f g rinv linv)    

/- The third equivalence exchanges equalities and isomorphisms. -/
@[hott]
def strpair_id_to_iso {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {a b : C} {α : std_str.P a} {β : std_str.P b} :
  (Σ (p : a = b), α =[p] β) ≃ (Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv) :=
let x := std_structure.mk a α, y := std_structure.mk b β in  
have po_hom : Π (p : a = b) (q : α =[p] β), std_str.H α β (idtoiso p).hom and 
                                            std_str.H β α (idtoiso p).inv, from 
  begin 
    intros p q, 
    hinduction p, 
    have q' : α = β, from eq_of_pathover_idp q,
    rwr idtoiso_refl_eq, rwr <- q',
    exact (std_str.id_H α, std_str.id_H α) 
  end, 
have idtoiso_hom_po : ∀ p : a = b, 
     (std_str.H α β (idtoiso p).hom and std_str.H β α (idtoiso p).inv) -> α =[p] β, from
  begin intros p H, hinduction p, apply pathover_idp_of_eq, exact std_str.std α β H end,                                            
have hom_po : Π (f : a ≅ b), (std_str.H α β f.hom and std_str.H β α f.inv) ->
                 α =[category.isotoid f] β, from 
  assume f H,
  have r : f = idtoiso (idtoiso⁻¹ᶠ f), by rwr category.idtoiso_rinv f,
  begin rwr r at H, exact idtoiso_hom_po (idtoiso⁻¹ᶠ f) H end,                                                             
let F := λ (pq : Σ (p : a = b), α =[p] β), 
         @dpair (a ≅ b) (λ f : a ≅ b, std_str.H α β f.hom and std_str.H β α f.inv) 
                (idtoiso pq.1) (po_hom pq.1 pq.2),
    G := λ iso_H : (Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv), 
         @dpair (a = b) (λ p : a = b, α =[p] β) 
                (category.isotoid iso_H.1) (hom_po iso_H.1 iso_H.2) in  
have rinv : ∀ (iso_H : Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv), 
            F (G iso_H) = iso_H, from 
  begin
    intro iso_H,
    fapply sigma_eq,
    { exact category.idtoiso_rinv iso_H.1 },
    { apply pathover_of_eq_tr, exact is_prop.elim _ _ }
  end,            
have linv : ∀ (pq : Σ (p : a = b), α =[p] β), G (F pq) = pq, from 
  begin
    intro pq,
    fapply sigma_eq,
    { exact category.idtoiso_linv pq.1 },
    { apply pathover_of_eq_tr, exact is_prop.elim _ _ }, 
  end,                                                             
equiv.mk F (adjointify F G rinv linv)  

/- The fourth equivalence splits up equalities of standard structure isomorphisms. -/
@[hott]
def iso_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {x y : std_structure std_str} (F : x ≅ y) : x.carrier ≅ ↑y :=
let f := (F.hom : x ⟶ y).1, g := F.inv.1 in
have rinv : g ≫ f = 𝟙 ↑y, by rwr <- comp_hom_std_C; rwr F.r_inv,
have linv : f ≫ g = 𝟙 ↑x, by rwr <- comp_hom_std_C; rwr F.l_inv, 
iso.mk f g rinv linv  

@[hott]
def str_iso_eq_comp {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {a b : C} {α : std_str.P a} {β : std_str.P b} :
  (Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv) ≃ 
  (std_structure.mk a α ≅ std_structure.mk b β) :=
begin
  let x := std_structure.mk a α, let y := std_structure.mk b β,
  fapply equiv.mk,
  /- We define `F : (Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv) -> (x ≅ y)`. -/
  { intro iso_H, 
    fapply iso.mk,
    { exact ⟨iso_H.1.hom, iso_H.2.1⟩ },
    { exact ⟨iso_H.1.inv, iso_H.2.2⟩ },
    { apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, hsimp, rwr iso_H.1.r_inv },
    { apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, hsimp, rwr iso_H.1.l_inv } },
  { fapply adjointify,
    /- Now we define `G : (x ≅ y) -> (Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv)`-/
    { intro f, 
      fapply sigma.mk,
      { exact iso_std_C f },
      { exact (f.hom.2, f.inv.2) } },
    /- `r_inv : ∀ f : x ≅ y, F (G f) = f` -/  
    { intro f,
      apply hom_eq_to_iso_eq, apply hom_eq_C_std _ _, 
      hsimp, refl },
    /- `l_inv : ∀ iso_H : (Σ (f : a ≅ b), std_str.H α β f.hom and std_str.H β α f.inv),` 
       `G (F iso_H)) = iso_H` -/  
    { intro iso_H, 
      fapply sigma_eq, 
      { apply hom_eq_to_iso_eq, refl },
      { apply pathover_of_eq_tr, exact is_prop.elim _ _ } } }
end    

/- The last equivalence introduces the structure components in standard structures isomorphies. -/
@[hott]
def std_str_comp_iso {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {x y : std_structure std_str} :
  (x ≅ y) ≃ (std_structure.mk x.carrier x.str ≅ std_structure.mk y.carrier y.str) :=
begin hinduction x with a α, hinduction y with b β, exact equiv.rfl end

/- Finally, we show that the composition of the five equivalences is `idtoiso`. -/
@[hott]
def comp_eqv_idtoiso {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {x y : std_structure std_str} :
  ∀ (p : x = y), (std_str_comp_iso.to_fun⁻¹ᶠ (str_iso_eq_comp.to_fun (strpair_id_to_iso.to_fun 
                            (std_str_eq_eta.to_fun (std_str_comp_eq.to_fun p))))) = idtoiso p :=                            
begin
  intro p, hinduction p, hinduction x with a α,
  let x := std_structure.mk a α,
  have p₁ : std_str_comp_eq.to_fun (refl x) = refl x, from rfl,
  have p₂ : std_str_eq_eta.to_fun (refl x) = ⟨refl a, idpo⟩, from rfl,
  have p₃ : strpair_id_to_iso.to_fun ⟨refl a, idpo⟩ = 
            ⟨id_is_iso a, (std_str.id_H α, std_str.id_H α)⟩, from rfl,
  have p₄ : str_iso_eq_comp.to_fun ⟨id_is_iso a, (std_str.id_H α, std_str.id_H α)⟩ = id_is_iso x,
    from begin apply hom_eq_to_iso_eq, refl end,         
  rwr idtoiso_refl_eq, rwr p₁, rwr p₂, rwr p₃, rwr p₄
end     

/- Now we can prove the equivalence and thus the Structure Identity Principle. -/
@[hott]
def std_str_eq_eqv_iso {C : Type u} [category.{v} C] {std_str : std_structure_on C} :
  ∀ x y : std_structure std_str, (x = y) ≃ (x ≅ y) :=
assume x y, std_str_comp_eq ⬝e std_str_eq_eta ⬝e strpair_id_to_iso ⬝e 
            str_iso_eq_comp ⬝e std_str_comp_iso⁻¹ᵉ 

@[hott, instance]
def structure_identity_principle {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  category (std_structure std_str) :=
have idtoiso_eq : ∀ x y : std_structure std_str, (std_str_eq_eqv_iso x y).to_fun = @idtoiso _ _ x y, from
  begin 
    intros x y, apply eq_of_homotopy, 
    intro p, exact comp_eqv_idtoiso p 
  end,      
have idtoiso_eqv : ∀ x y : std_structure std_str, is_equiv (@idtoiso _ _ x y), from 
  assume x y,
  have eqv : is_equiv (std_str_eq_eqv_iso x y).to_fun, from (std_str_eq_eqv_iso x y).to_is_equiv,
  by rwr idtoiso_eq x y at eqv; exact eqv, 
category.mk idtoiso_eqv

/- The forgetful functor from a category of standard structures to the underlying category -/
@[hott]
def forget_str {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  (std_structure std_str) ⥤ C :=
begin
  fapply functor.mk,  
  { exact λ x, x.carrier },  -- map of objects
  { intros x y f, exact f.1 },  -- map of morphisms
  { intro x, exact idhom_std_C x },  -- preserves identity morphisms
  { intros x y z f g, exact comp_hom_std_C f g }  -- preserves compositions of morphisms 
end 

/- The forgetful functor is faithful. -/
@[hott]
def forget_is_faithful {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  is_faithful_functor _ _ (forget_str std_str) :=
begin intros x y, exact pred_Set_map_is_inj _ end  

/- The forgetful functor composed with a functor to a category of standard structures -/
@[hott]
def forget {J : Type.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  {std_str : std_structure_on C} (F : J ⥤ std_structure std_str) : J ⥤ C :=
F ⋙ (forget_str std_str)  

/- The full subcategory of a subtype of a category. -/
@[hott, instance]
def subtype_has_hom {C : Type u} [category.{v} C] (P : C -> trunctype.{0} -1) :
  has_hom (subtype (λ c : C, ↥(P c))) :=
begin fapply has_hom.mk, intros sc₁ sc₂, exact sc₁.1 ⟶ sc₂.1 end

@[hott, instance]
def subtype_cat_struct {C : Type u} [category.{v} C] (P : C -> trunctype.{0} -1) :
  category_struct (subtype (λ c : C, ↥(P c))) :=
begin
  fapply category_struct.mk,
  { intro sc, exact 𝟙 sc.1 },
  { intros sc₁ sc₂ sc₃ f g, exact f ≫ g }
end    

@[hott, instance]
def full_subprecat_on_subtype {C : Type u} [category.{v} C] (P : C -> trunctype.{0} -1) :
  precategory (subtype (λ c : C, ↥(P c))) :=
begin  
  fapply precategory.mk,
  { intros sc₁ sc₂ f, hsimp },
  { intros sc₁ sc₂ f, hsimp },
  { intros sc₁ sc₂ sc₃ sc₄ f g h, hsimp, refl }
end  

end categories

end hott