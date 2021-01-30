import setalgebra

universes v u w
hott_theory

namespace hott
open hott.set hott.subset 

/-
We introduce precategories and categories following the HoTT book, 
Sec. 9.1. HoTT precategories have sets of homomorphisms, and HoTT categories 
prescribe univalence : Isomorphisms are equivalent to identities of objects.

As far as possble we copy the mathlib-code in [category_theory.category.default].
-/

namespace category_theory

/-- A 'notation typeclass' on the way to defining a precategory. -/
@[hott]
class obj_hom :=
(obj : Type u) 
(hom : obj → obj → Set.{v})

infixr ` ⟶ `:10 := obj_hom.hom  -- type as \h

/-- A preliminary structure on the way to defining a precategory,
containing the data, but none of the axioms. -/
@[hott]
class category_struct extends obj_hom.{v u} :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

/-- The sructure of a precategory. -/
@[hott]
class precategory extends category_struct.{v u} :=
(id_comp : ∀ {X Y : obj} (f : hom X Y), 𝟙 X ≫ f = f)
(comp_id : ∀ {X Y : obj} (f : hom X Y), f ≫ 𝟙 Y = f)
(assoc   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  (f ≫ g) ≫ h = f ≫ (g ≫ h))

attribute [hsimp] precategory.id_comp precategory.comp_id precategory.assoc


@[hott]
instance cat_to_obj : has_coe_to_sort precategory.{v u} :=
  has_coe_to_sort.mk (Type u) (λ S, S.obj)

/- Defintion of categorical isomorphisms. -/
@[hott]
class is_iso {C : precategory.{v u}} {a b : C} (f : a ⟶ b) :=
  mk' :: (inv : b ⟶ a) 
         (r_inv : inv ≫ f = 𝟙 b) 
         (l_inv : f ≫ inv = 𝟙 a)

attribute [reducible] is_iso.inv

@[hott]
structure iso [C : precategory.{v u}] (a b : C) :=
  (to_hom : a ⟶ b)
  (to_is_iso : is_iso to_hom)  

postfix `⁻¹ʰ`:std.prec.max_plus := iso.inv

section
variables [C : precategory.{v u}] {a b : C}

infix ` ≅ `:25 := iso
attribute [instance] iso.to_is_iso

@[hott]
instance : has_coe_to_fun (a ≅ b) := 
  ⟨_, iso.to_hom⟩ 

@[hott]
def id_is_iso (a : C) : a ≅ a :=
  sorry

end

@[hott]
def idtoiso [C : precategory.{v u}] (a b : C) : (a = b) -> (a ≅ b) :=
  begin intro eq, induction eq, exact id_is_iso a end

end category_theory

end hott