import setalgebra pathover2

universes v u w
hott_theory

namespace hott
open hott.set hott.subset hott.is_trunc hott.is_equiv

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

/- Isomorphisms are uniquely determined by their underlying homomorphism:
   The inverse map by functorial equalities, and the functorial equailities 
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
def idtoiso {C : Type u} [precategory.{v} C] (a b : C) : (a = b) -> (a ≅ b) :=
  begin intro eq, hinduction eq, exact id_is_iso a end

/-- The structure of a category. -/
@[hott]
class category (obj : Type u) extends precategory.{v} obj :=
(ideqviso : ∀ a b : obj, is_equiv (idtoiso a b)) 

attribute [instance] category.ideqviso

section
universes v' u'
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

attribute [simp] functor.map_id
attribute [simp] functor.map_comp

end

/- To construct the opposite category, we use the mathlib-trick in [data.opposite]
   that allows the elaborator to do most of the work. -/  
variables {C : Type u}   

@[hott]
def opposite : Type u := C 

notation C `ᵒᵖ`:std.prec.max_plus := @opposite C

namespace opposite

/-- The canonical map `C → Cᵒᵖ`. -/
@[hott]
def op : C → Cᵒᵖ := hott.set.id
/-- The canonical map `Cᵒᵖ → C`. -/
@[hott]
def unop : Cᵒᵖ → C := hott.set.id

@[hott, hsimp]
def op_inj_iff (x y : C) : op x = op y ↔ x = y := iff.rfl

@[hott, hsimp] 
def unop_inj_iff (x y : Cᵒᵖ) : unop x = unop y ↔ x = y := iff.rfl

@[hott, hsimp] 
def op_unop (x : Cᵒᵖ) : op (unop x) = x := rfl

@[hott, hsimp] 
def unop_op (x : C) : unop (op x) = x := rfl

attribute [irreducible] opposite

end opposite

open opposite

@[hott]
instance has_hom.opposite [has_hom.{v} C] : has_hom Cᵒᵖ :=
  has_hom.mk (λ x y, unop y ⟶ unop x) /- Why can't we define a `has_hom` structure with `{}`? -/

/- The opposite of a morphism in `C`. -/
@[hott]
def hom_op [has_hom.{v} C] {x y : C} (f : x ⟶ y) : op y ⟶ op x := f
/- Given a morphism in `Cᵒᵖ`, we can take the "unopposite" back in `C`. -/
@[hott]
def hom_unop [has_hom.{v} C] {x y : Cᵒᵖ} (f : x ⟶ y) : unop y ⟶ unop x := f

attribute [irreducible] has_hom.opposite /- Why can't you change this name to `has_hom_opp`? -/

@[hott, hsimp] 
def hom_unop_op [has_hom.{v} C] {x y : C} {f : x ⟶ y} : hom_unop (hom_op f) = f := rfl

@[hott, hsimp] 
def hom_op_unop [has_hom.{v} C] {x y : Cᵒᵖ} {f : x ⟶ y} : hom_op (hom_unop f) = f := rfl

/- The opposite precategory. -/
@[hott, instance]
def category_struct.opposite [precategory.{v} C] : category_struct.{v} Cᵒᵖ :=
  category_struct.mk (λ x, hom_op (𝟙 (unop x))) 
                     (λ _ _ _ f g, hom_op (hom_unop g ≫ hom_unop f))

@[hott]
def id_comp_op [precategory.{v} C] : ∀ (x y : Cᵒᵖ) (f : x ⟶ y), 𝟙 x ≫ f = f := 
begin intros x y f, hsimp end
   

@[hott]
def comp_id_op [precategory.{v} C] : ∀ (x y : Cᵒᵖ) (f : x ⟶ y), f ≫ 𝟙 y = f := 
begin intros x y f, hsimp end

@[hott]
def assoc_op [precategory.{v} C] : ∀ (x y z w : Cᵒᵖ) (f : x ⟶ y) (g : y ⟶ z) (h : z ⟶ w), 
  (f ≫ g) ≫ h = f ≫ g ≫ h := 
begin 
  intros x y z w f g h, 
  change hom_op (hom_unop h ≫ hom_unop (hom_op (hom_unop g ≫ hom_unop f))) = 
         hom_op (hom_unop (hom_op (hom_unop h ≫ hom_unop g)) ≫ hom_unop f),
  hsimp       
end  

@[hott, instance]
def precategory.opposite [precategory.{v} C] : precategory.{v} Cᵒᵖ :=
  precategory.mk id_comp_op comp_id_op assoc_op                   

/- The opposite category. 
   We show the equivalence by splitting it up in three steps and using that maps from 
   `a = b` are determined by `rfl` if `a` and `b` are allowed to vary freely. -/
@[hott, hsimp]
def id_op_to_id [precategory.{v} C] : Π {a b : Cᵒᵖ}, (a = b) -> (unop a = unop b) :=
  begin intros a b p, hinduction p, exact rfl end  

@[hott, hsimp]
def id_to_id_op [precategory.{v} C] : Π {a b : Cᵒᵖ}, (unop a = unop b) -> (a = b) :=
  assume a b p_op, 
  calc a   = op (unop a) : by hsimp
       ... = op (unop b) : ap op p_op 
       ... = b : op_unop b 

@[hott, instance]
def id_op_eqv_id [precategory.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@id_op_to_id _ _ a b) :=
  assume a b,
  have rinv : ∀ p_op : unop a = unop b, id_op_to_id (id_to_id_op p_op) = p_op, from  
    begin intro p_op, hsimp, rwr ap_compose', hsimp end, 
  have linv : ∀ p : a = b, id_to_id_op (id_op_to_id p) = p, from 
    begin intro p, hsimp, rwr ap_compose', hsimp end,
  is_equiv.adjointify id_op_to_id id_to_id_op rinv linv   

@[hott, hsimp]
def iso_to_iso_op [precategory.{v} C] : ∀ {a b : Cᵒᵖ}, (unop a ≅ unop b) -> (a ≅ b) :=
begin 
  intros a b i,
  fapply iso.mk, 
    rwr <- op_unop a, rwr <- op_unop b, exact hom_op i.inv,
    rwr <- op_unop a, rwr <- op_unop b, exact hom_op i.hom,
    change hom_op (i.inv ≫ i.hom) = hom_op (𝟙 (unop b)), apply ap hom_op, exact i.r_inv,
    change hom_op (i.hom ≫ i.inv) = hom_op (𝟙 (unop a)), apply ap hom_op, exact i.l_inv   
end

@[hott, hsimp]
def iso_op_to_iso [precategory.{v} C] : ∀ {a b : Cᵒᵖ}, (a ≅ b) -> (unop a ≅ unop b) :=
begin
  intros a b i,
  fapply iso.mk,
    exact hom_unop i.inv,
    exact hom_unop i.hom,
  { rwr <- @hom_unop_op _ _ _ _ (hom_unop i.hom ≫ hom_unop i⁻¹ʰ),  
    rwr <- @hom_unop_op _ _ _ _ (𝟙 (unop b)), exact ap hom_unop (i.r_inv) },
  { rwr <- @hom_unop_op _ _ _ _ (hom_unop i⁻¹ʰ ≫ hom_unop i.hom),  
    rwr <- @hom_unop_op _ _ _ _ (𝟙 (unop a)), exact ap hom_unop (i.l_inv) }
end  

@[hott, instance]
def iso_eqv_iso_op [precategory.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (@iso_to_iso_op _ _ a b) :=
  assume a b,
  have rinv : ∀ h : a ≅ b, iso_to_iso_op (iso_op_to_iso h) = h, from 
    assume h, 
    have hom_eq : (iso_to_iso_op (iso_op_to_iso h)).hom = h.hom, by hsimp, 
    hom_eq_to_iso_eq hom_eq,
  have linv : ∀ h_op : unop a ≅ unop b, iso_op_to_iso (iso_to_iso_op h_op) = h_op, from 
    assume h_op,
    have hom_eq : (iso_op_to_iso (iso_to_iso_op h_op)).hom = h_op.hom, by hsimp,
    hom_eq_to_iso_eq hom_eq,    
  is_equiv.adjointify iso_to_iso_op iso_op_to_iso rinv linv

/- This lemma should belong to [init.path]. Needs function extensionality. -/
@[hott]
def fn_id_rfl {A : Type u} {B : A -> A -> Type v} 
  (f g : ∀ {a b : A}, (a = b) -> B a b) : 
  (∀ a : A, f (@rfl _ a) = g (@rfl _ a)) -> ∀ a b : A, @f a b = @g a b :=
assume fn_rfl_eq,
have fn_hom_eq : ∀ (a b : A) (p : a = b), @f a b p = @g a b p, from 
  begin intros a b p, hinduction p, exact fn_rfl_eq a end,  
assume a b, 
eq_of_homotopy (fn_hom_eq a b) 

@[hott]
def idtoiso_rfl_eq [category.{v} C] : ∀ a : Cᵒᵖ, 
  iso_to_iso_op (idtoiso (unop a) (unop a) (id_op_to_id (@rfl _ a))) = 
  idtoiso a a (@rfl _ a) :=
begin intro a, apply hom_eq_to_iso_eq, change 𝟙 a = 𝟙 a, refl end 

@[hott, instance]
def ideqviso_op [category.{v} C] : ∀ a b : Cᵒᵖ, is_equiv (idtoiso a b) :=
  assume a b,
  let f := @id_op_to_id _ _ a b, g := @idtoiso _ _ (unop a) (unop b), 
      h := @iso_to_iso_op _ _ a b in
  have id_optoiso_op : is_equiv (h ∘ g ∘ f), from is_equiv_compose h (g ∘ f), 
  let hgf := λ (a b : Cᵒᵖ) (p : a = b), 
             iso_to_iso_op (idtoiso (unop a) (unop b) (id_op_to_id p)) in
  have idtoiso_eq : hgf a b = @idtoiso _ _ a b, from fn_id_rfl _ _ idtoiso_rfl_eq a b,
  begin rwr <- idtoiso_eq; exact id_optoiso_op end

@[hott, instance]
def category.opposite [category.{v} C] : category.{v} Cᵒᵖ :=
  category.mk ideqviso_op 

end category_theory

end hott