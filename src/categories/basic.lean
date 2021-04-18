import setalgebra pathover2 set_axioms

universes v u v' u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv

/-
We introduce precategories and categories following the HoTT book, 
Sec. 9.1. HoTT precategories have sets of homomorphisms, and HoTT categories 
prescribe univalence : Isomorphisms are equivalent to identities of objects.

As far as possible we copy the mathlib-code in [category_theory.category.default].
-/

namespace categories

/-- A 'notation typeclass' on the way to defining a precategory. -/
@[hott]
class has_hom (obj : Type u) : Type (max u (v+1)):=
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
  (g : c ⟶ a) (h : c ⟶ b) : g ≫ i.hom = h  -> g = h ≫ i.inv :=
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
have r_inv_eq : i.r_inv =[ap011 R hom_eq inv_eq; set.id] j.r_inv, from 
  begin apply pathover_of_tr_eq, apply is_set.elim end,
have l_inv_eq : i.l_inv =[ap011 L hom_eq inv_eq; set.id] j.l_inv, from 
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


/-- The structure of a category. -/
@[hott]
class category (obj : Type u) extends precategory.{v} obj :=
(ideqviso : ∀ a b : obj, is_equiv (@idtoiso _ _ a b)) 

attribute [instance] category.ideqviso

@[hott]
def category.isotoid {obj : Type u} [category.{v} obj] : 
  Π {a b : obj}, a ≅ b -> a = b :=
assume a b iso,  
@is_equiv.inv _ _ _ (category.ideqviso a b) iso  

@[hott]
def category.idtoiso_rinv {obj : Type u} [category.{v} obj] {a b : obj} :
  ∀ i : a ≅ b, idtoiso (idtoiso⁻¹ᶠ i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott]
def category.idtoiso_linv {obj : Type u} [category.{v} obj] {a b : obj} :
  ∀ p : a = b, idtoiso⁻¹ᶠ (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b) 

@[hott]
def iso_hom_tr_comp {C : Type u} [category.{v} C] {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : c₁ ⟶ d) : (idtoiso⁻¹ᶠ i) ▸ h = i⁻¹ʰ ≫ h :=
begin 
  rwr <-(category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp (idtoiso⁻¹ᶠ i) h
end 

section
variables (C : Type u) (D : Type u')

/- Functors are defined between precategories. -/
@[hott]
structure functor [precategory.{v} C] [precategory.{v'} D] :
  Type (max v v' u u') :=
(obj      : C → D)
(map      : Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)))
(map_id   : ∀ (x : C), map (𝟙 x) = 𝟙 (obj x))
(map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = (map f) ≫ (map g))

infixr ` ⥤ `:26 := functor       

attribute [hsimp] functor.map_id
attribute [hsimp] functor.map_comp

@[hott]
def constant_functor [precategory.{v} C] [precategory.{v'} D] (d : D) : 
  C ⥤ D := 
have id_hom_eq : ∀ d : D, 𝟙 d = 𝟙 d ≫ 𝟙 d, by intro d; hsimp,  
functor.mk (λ c : C, d) (λ c₁ c₂ f, 𝟙 d) (λ c, rfl) 
  (λ c₁ c₂ c₃ f g, (id_hom_eq d))

@[hott]
structure nat_trans [precategory.{v} C] [precategory.{v'} D] (F G : C ⥤ D) :=
(app : Π c : C, (F.obj c) ⟶ (G.obj c))
(naturality : ∀ {c c' : C} (f : c ⟶ c'), 
                                 (F.map f) ≫ (app c') = (app c) ≫ (G.map f))  

infixr ` ⟹ `:10 := nat_trans _ _

/- We now define structures on categories and prove the Structure Identity Principle, following
   the [HoTT-Book], Section 9.8. -/
@[hott]
structure std_structure_on (C : Type u) [category.{v} C] :=
  (P : C -> Type u)
  (H : Π {x y : C} (α : P x) (β : P y) (f : x ⟶ y), trunctype.{u} -1)
  (id_H : ∀ {x : C} (α : P x), H α α (𝟙 x))
  (comp_H : ∀ {x y z : C} (α : P x) (β : P y) (γ : P z) (f : x ⟶ y) (g : y ⟶ z), 
              H α β f -> H β γ g -> H α γ (f ≫ g))
  (std : ∀ {x y : C} (α β : P x) , H α β (𝟙 x) -> H β α (𝟙 x) -> α = β)           

@[hott]
structure std_structure {C : Type u} [category.{v} C] (std_str : std_structure_on C) :=
  (carrier : C)
  (str : std_str.P carrier)

@[hott]
instance {C : Type u} [category.{v} C] (std_str : std_structure_on C) : 
  has_coe (std_structure std_str) C :=
⟨λ x : std_structure std_str, x.carrier⟩  

@[hott, instance]
def std_str_has_hom {C : Type u} [category.{u} C] (std_str : std_structure_on C) :
  has_hom (std_structure std_str) := 
has_hom.mk (λ (x y : std_structure std_str), 
            ↥{ f ∈ (x.carrier ⟶ y) | std_str.H (x.str) (y.str) f })

@[hott]
instance hom_std_C {C : Type u} [category.{u} C] {std_str : std_structure_on C}
  {x y : std_structure std_str} : has_coe ↥(x ⟶ y) ↥(x.carrier ⟶ y.carrier) :=
⟨λ f, { f ∈ (x.carrier ⟶ y) | std_str.H (x.str) (y.str) f }.map f⟩  

@[hott]
def hom_H {C : Type u} [category.{u} C] {std_str : std_structure_on C} 
  {x y : std_structure std_str} :
  Π f : x ⟶ y, std_str.H x.str y.str (↑f) :=
assume f, f.2              

@[hott]
def hom_eq_C_std {C : Type u} [category.{u} C] {std_str : std_structure_on C} 
  {x y : std_structure std_str} (f g : x ⟶ y) : 
  (↑f = (↑g : x.carrier ⟶ y.carrier)) -> (f = g) :=
sorry  

@[hott, instance]
def std_str_cat_struct {C : Type u} [category.{u} C] (std_str : std_structure_on C) :
  category_struct (std_structure std_str) :=
category_struct.mk (λ x : std_structure std_str, elem_pred (𝟙 ↑x) (std_str.id_H x.str)) 
  (λ (x y z : std_structure std_str) (f : x ⟶ y) (g : y ⟶ z), 
   elem_pred (↑f ≫ ↑g) (std_str.comp_H x.str y.str z.str ↑f ↑g (hom_H f) (hom_H g))) 

@[hott]
def idhom_std_C {C : Type u} [category.{u} C] {std_str : std_structure_on C} 
  (x : std_structure std_str) : ↑(𝟙 x) = 𝟙 x.carrier :=
sorry  

@[hott]
def comp_hom_std_C {C : Type u} [category.{u} C] {std_str : std_structure_on C} 
  {x y z : std_structure std_str} (f : x ⟶ y) (g : y ⟶ z) : 
  ↑(f ≫ g) = (↑f : x.carrier ⟶ y.carrier) ≫ (↑g : y.carrier ⟶ z.carrier) :=
sorry  

@[hott, instance]
def std_str_precategory {C : Type u} [category.{u} C] (std_str : std_structure_on C) :
  precategory (std_structure std_str) :=
have ic : ∀ (x y : std_structure std_str) (f : x ⟶ y), 𝟙 x ≫ f = f, from 
  begin intros x y f, apply hom_eq_C_std _ _, rwr comp_hom_std_C, hsimp end,
have ci : ∀ (x y : std_structure std_str) (f : x ⟶ y), f ≫ 𝟙 y = f, from 
  begin intros x y f, apply hom_eq_C_std _ _, rwr comp_hom_std_C, hsimp end,
have as : ∀ (x y z w: std_structure std_str) (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ w),
          (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
  begin intros x y z w f g h, apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, hsimp end,
precategory.mk ic ci as          

end

end categories

end hott