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
@[hott]
class precategory (obj : Type u) 
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
def id_is_iso {C : Type u} [precategory.{v} C] (a : C) : a ≅ a := 
  have inv_eq : 𝟙 a ≫ 𝟙 a = 𝟙 a, from precategory.id_comp (𝟙 a),
  iso.mk (𝟙 a) (𝟙 a) inv_eq inv_eq

@[hott]
def idtoiso {C : Type u} [precategory.{v} C] (a b : C) : (a = b) -> (a ≅ b) :=
  begin intro eq, induction eq, exact id_is_iso a end

/-- The structure of a category. -/
@[hott]
class category (obj : Type u) extends precategory.{v} obj :=
(ideqviso : ∀ a b : obj, is_equiv (idtoiso a b)) 

/- To construct the opposite category, we use the mathlib-trick in [data.opposite]
   that allows the elaborator to do most of the work. -/
@[hott]
def opposite (C : Type u): Type u := C 

notation C `ᵒᵖ`:std.prec.max_plus := opposite C

namespace opposite

variables {C : Type u}
/-- The canonical map `α → αᵒᵖ`. -/
@[hott]
def op : C → Cᵒᵖ := hott.set.id
/-- The canonical map `αᵒᵖ → α`. -/
@[hott]
def unop : Cᵒᵖ → C := hott.set.id

@[hott]
lemma op_injective : function.injective (op : C → Cᵒᵖ) := λ _ _, id

@[hott]
lemma unop_injective : function.injective (unop : Cᵒᵖ → C) := λ _ _, id

@[hott, hsimp]
lemma op_inj_iff (x y : C) : op x = op y ↔ x = y := iff.rfl

@[hott, hsimp] 
lemma unop_inj_iff (x y : Cᵒᵖ) : unop x = unop y ↔ x = y := iff.rfl

@[hott, hsimp] 
lemma op_unop (x : Cᵒᵖ) : op (unop x) = x := rfl

@[hott, hsimp] 
lemma unop_op (x : C) : unop (op x) = x := rfl

attribute [irreducible] opposite

end opposite

end category_theory

end hott