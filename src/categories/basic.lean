import sets.algebra init2 types2 sets.axioms categories.precat

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.precategories

/-
We introduce precategories and categories following the HoTT book, 
Sec. 9.1. HoTT precategories have sets of homomorphisms, and HoTT categories 
prescribe univalence : Isomorphisms are equivalent to identities of objects.

As far as possible we copy the mathlib-code in [category_theory.category.default]. In particular,
we keep the distinction of universe levels for objects and morphisms of a category.
-/

namespace categories

/- Definition of categorical isomorphisms. -/
@[hott]
structure is_iso {C : Type u} [is_precat.{v} C] {a b : C} (f : a ⟶ b) :=
  (inv : b ⟶ a)
  (r_inv : inv ≫ f = 𝟙 b)
  (l_inv : f ≫ inv = 𝟙 a)

@[hott, instance]
def is_iso_is_prop {C : Type u} [HP :is_precat.{v} C] {a b : C} 
  (f : a ⟶ b) : is_prop (is_iso f) :=
begin
  apply is_prop.mk, intros is_iso₁ is_iso₂,
  hinduction is_iso₁ with inv₁ r_inv₁ l_inv₁,
  hinduction is_iso₂ with inv₂ r_inv₂ l_inv₂,
  fapply apd0111' is_iso.mk, 
  { rwr <- @is_precat.comp_id _ HP _ _ inv₁, rwr <- l_inv₂,
    rwr <- @is_precat.assoc _ HP, rwr r_inv₁, 
    rwr @is_precat.id_comp _ HP _ _ inv₂ },
  all_goals { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end

@[hott]
structure iso {C : Type u} [is_precat.{v} C] (a b : C) :=
  (hom : a ⟶ b)
  (ih : is_iso hom)

infix ` ≅ `:25 := iso

@[hott]
instance iso_to_hom {C : Type u} [is_precat.{v} C] (a b : C) : 
  has_coe_to_fun (a ≅ b) :=
has_coe_to_fun.mk (λ _, a ⟶ b) (λ i, i.hom)

@[hott, hsimp]
def inv_iso {C : Type u} [is_precat.{v} C] {a b : C} (i : a ≅ b) : b ≅ a :=
  iso.mk i.ih.inv 
         (is_iso.mk i.hom i.ih.l_inv i.ih.r_inv)

postfix `⁻¹ʰ`:std.prec.max_plus := inv_iso 

/- Calculation rules for isomorphisms. -/
@[hott, hsimp]
def iso_inv_inv {C : Type u} [is_precat.{v} C] {a b : C} (i : a ≅ b) :
  (inv_iso i)⁻¹ʰ = i :=
by hinduction i with hom iso_hom; hinduction iso_hom; hsimp 

@[hott, hsimp]
def iso_rcancel {C : Type u} [is_precat.{v} C] {a b c : C} (i : a ≅ b)
  {g h : c ⟶ a} : g ≫ i.hom = h ≫ i.hom -> g = h :=
assume pc, 
have pc_inv : (g ≫ i.hom) ≫ i.ih.inv = (h ≫ i.hom) ≫ i.ih.inv, from 
  ap (λ h : c ⟶ b, h ≫ i.ih.inv) pc,
calc   g = g ≫ 𝟙 a : by hsimp
     ... = g ≫ (i.hom ≫ i.ih.inv) : by rwr <- i.ih.l_inv
     ... = (g ≫ i.hom) ≫ i.ih.inv : by hsimp
     ... = (h ≫ i.hom) ≫ i.ih.inv : by rwr pc_inv
     ... = h ≫ (i.hom ≫ i.ih.inv) : by hsimp
     ... = h ≫ 𝟙 a : by rwr i.ih.l_inv     
     ... = h : by hsimp 

@[hott, hsimp]
def iso_lcancel {C : Type u} [is_precat.{v} C] {a b c : C} (i : a ≅ b)
  {g h : b ⟶ c} : i.hom ≫ g = i.hom ≫ h -> g = h :=
assume cp, 
have cp_inv : i.ih.inv ≫ (i.hom ≫ g) = i.ih.inv ≫ (i.hom ≫ h), from 
  ap (λ h : a ⟶ c, i.ih.inv ≫ h) cp,
calc   g = 𝟙 b ≫ g : by hsimp
     ... = (i.ih.inv ≫ i.hom) ≫ g : by rwr <-i.ih.r_inv
     ... = i.ih.inv ≫ (i.hom ≫ g) : by hsimp
     ... = i.ih.inv ≫ (i.hom ≫ h) : by rwr cp_inv
     ... = (i.ih.inv ≫ i.hom) ≫ h : by hsimp
     ... = 𝟙 b ≫ h : by rwr i.ih.r_inv     
     ... = h : by hsimp 

@[hott, hsimp]
def iso_move_lr {C : Type u} [is_precat.{v} C] {a b c : C} (i : a ≅ b)
  (g : b ⟶ c) (h : a ⟶ c) : i.hom ≫ g = h -> g = i.ih.inv ≫ h :=
assume pcr,
have i.ih.inv ≫ i.hom ≫ g = i.ih.inv ≫ h, from 
  ap (λ h : a ⟶ c, i.ih.inv ≫ h) pcr,
calc g   = 𝟙 b ≫ g : by hsimp
     ... = (i.ih.inv ≫ i.hom) ≫ g : by rwr <- i.ih.r_inv
     ... = i.ih.inv ≫ (i.hom ≫ g) : by hsimp
     ... = i.ih.inv ≫ h : by rwr pcr   

@[hott, hsimp]
def iso_move_rl {C : Type u} [is_precat.{v} C] {a b c : C} (i : a ≅ b)
  (g : c ⟶ a) (h : c ⟶ b) : g ≫ i.hom = h -> g = h ≫ i.ih.inv :=
assume pcl,
have (g ≫ i.hom) ≫ i.ih.inv = h ≫ i.ih.inv, from 
  ap (λ h : c ⟶ b, h ≫ i.ih.inv) pcl,
calc g   = g ≫ 𝟙 a : by hsimp
     ... = g ≫ (i.hom ≫ i.ih.inv) : by rwr <-i.ih.l_inv
     ... = (g ≫ i.hom) ≫ i.ih.inv : by hsimp
     ... = h ≫ i.ih.inv : by rwr pcl     

/- Isomorphisms are uniquely determined by their underlying homomorphism:
   The inverse map by functorial equalities, and the functorial equalities 
   because the types of homomorphisms are sets. -/
@[hott]
def hom_eq_to_iso_eq {C : Type u} [is_precat.{v} C] {a b : C} {i j : a ≅ b} :
  i.hom = j.hom -> i = j :=
begin
  hinduction i, hinduction j,
  intro hom_eq, fapply apd011 iso.mk, 
  exact hom_eq, apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott, hsimp]
def id_iso {C : Type u} [is_precat.{v} C] (a : C) : a ≅ a := 
  have inv_eq : 𝟙 a ≫ 𝟙 a = 𝟙 a, from is_precat.id_comp (𝟙 a),
  iso.mk (𝟙 a) (is_iso.mk (𝟙 a) inv_eq inv_eq)

@[hott, hsimp]
def idtoiso {C : Type u} [is_precat.{v} C] {a b : C} : (a = b) -> (a ≅ b) :=
  begin intro eq, exact eq ▸[λ c, a ≅ c] id_iso a end

/- `idtoiso` is natural. -/
@[hott, hsimp]
def idtoiso_refl_eq {C : Type u} [is_precat.{v} C] (a : C) : idtoiso (refl a) = id_iso a :=
  by hsimp

@[hott]
def id_inv_iso_inv {C : Type u} [is_precat.{v} C] {c₁ c₂ : C} (p : c₁ = c₂) :
  idtoiso p⁻¹ = inv_iso (idtoiso p) := 
begin hinduction p, refl end 

@[hott]
def idtoiso_comp_eq {C : Type u} [is_precat.{v} C] {c₁ c₂ c₃ : C} 
  (p : c₁ = c₂) (q : c₂ = c₃) : 
  (idtoiso p).hom ≫ (idtoiso q).hom = (idtoiso (p ⬝ q)).hom :=
begin hinduction p, hinduction q, hsimp end   

/- `idtoiso` commutes with functors -/
@[hott]
def funct_idtoiso {C : Type _} [is_precat C] {c₁ c₂ : C} 
  {D : Type _} [is_precat D] (F : C ⥤ D) (p : c₁ = c₂) :
  F.map (idtoiso p).hom = (idtoiso (ap F.obj p)).hom :=
begin 
  hinduction p, rwr idtoiso_refl_eq, rwr ap_idp, 
  rwr idtoiso_refl_eq, change F.map (𝟙 c₁) = _, rwr F.map_id 
end  

/- The next two facts correspond to [HoTT-Book, Lem.9.1.9]. -/
@[hott]
def id_hom_tr_comp {C : Type u} [is_precat.{v} C] {c₁ c₂ d : C} 
  (p : c₁ = c₂) (h : c₁ ⟶ d) : p ▸ h = (idtoiso p)⁻¹ʰ.hom ≫ h :=
begin hinduction p, hsimp end   

@[hott]
def id_hom_tr_comp' {C : Type u} [is_precat.{v} C] {c₁ c₂ d : C}
  (p : c₁ = c₂) (h : d ⟶ c₁) : p ▸ h = h ≫ (idtoiso p).hom :=
begin hinduction p, hsimp end 

/- We can use `idtoiso` to describe equality of the maps on 
   homorphisms induced by an equality of functors. -/
@[hott]
def functor_map_eq {C : Type _} [is_precat C] {D : Type _} 
  [is_precat D] {F G : C ⥤ D} (p : F = G) {x y : C} : Π (f : x ⟶ y), 
  G.map f = (idtoiso (ap10 (ap functor.obj p) x)⁻¹).hom ≫
            F.map f ≫ (idtoiso (ap10 (ap functor.obj p) y)).hom :=   
begin intro f, hinduction p, hsimp end

/-- The structure of a category and the bundled category. -/
@[hott]
class is_cat (obj : Type u) extends is_precat.{v} obj :=
(ideqviso : ∀ a b : obj, is_equiv (@idtoiso _ _ a b)) 

attribute [instance] is_cat.ideqviso

@[hott]
structure Category :=
  (obj : Type u)
  (struct : is_cat obj)

@[hott] instance : has_coe_to_sort Category := 
  has_coe_to_sort.mk Type.{u} Category.obj

@[hott] 
def Cat.to_Precat : Category -> Precategory :=
  λ C, Precategory.mk C.obj C.struct.to_is_precat

attribute [instance] Category.struct

@[hott, hsimp]
def category.isotoid {C : Category} : 
  Π {a b : C}, a ≅ b -> a = b :=
assume a b iso,  
@is_equiv.inv _ _ _ (is_cat.ideqviso a b) iso  

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
  Π (a : C), category.isotoid (id_iso a) = refl a :=
begin intro a, rwr <- idtoiso_refl_eq a, exact category.idtoiso_linv (refl a) end 

@[hott]
def iso_hom_tr_comp {C : Category} {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : c₁ ⟶ d) : (idtoiso⁻¹ᶠ i) ▸ h = i⁻¹ʰ.hom ≫ h :=
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

/- A modified criterion for equality of functors -/
@[hott]
def functor_eq' {A : Type _} [is_precat A] {B : Type _} [is_precat B] 
  {F G : A ⥤ B} : Π (p : Π (x : A), F.obj x = G.obj x), 
    (Π {x y : A} (f : x ⟶ y), (idtoiso (p x)⁻¹).hom ≫ F.map f ≫ 
       (idtoiso (p y)).hom = G.map f) -> F = G :=
begin
  intros obj_eq map_eq, fapply functor_eq,
  { exact eq_of_homotopy obj_eq },
  { fapply dep_eq_of_homotopy3, intros x y h,
    apply pathover_of_tr_eq, 
    apply @tr_fn2_of_ap_tr_ap_tr _ _ _ _ _ _ (eq_of_homotopy obj_eq) 
            (λ b₁ b₂, b₁ ⟶ b₂) (F.map h) (G.map h), 
    rwr <- map_eq h, rwr ap10_eq_of_homotopy, rwr id_hom_tr_comp,
    rwr id_hom_tr_comp', rwr <- id_inv_iso_inv, rwr is_precat.assoc }
end

@[hott]
def functor_eq_obj' {A : Type _} [is_precat A] {B : Type _} [is_precat B] 
  {F G : A ⥤ B} (p : Π (x : A), F.obj x = G.obj x) 
    (q : Π {x y : A} (f : x ⟶ y), (idtoiso (p x)⁻¹).hom ≫ F.map f ≫ 
       (idtoiso (p y)).hom = G.map f) : 
  ap functor.obj (functor_eq' p @q) = eq_of_homotopy p :=
begin change ap _ (functor_eq _ _) = _, rwr functor_eq_obj end

end categories

end hott