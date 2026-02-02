import categories.precat

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

@[hott, hsimp]
def iso_inv_move_lr {C : Type u} [is_precat.{v} C] {a b c : C} (i : a ≅ b)
  (g : b ⟶ c) (h : a ⟶ c) : i.ih.inv ≫ h = g -> h = i.hom ≫ g :=
assume pcr,
have i.hom ≫ i.ih.inv ≫ h = i.hom ≫ g, from 
  ap (λ g : b ⟶ c, i.hom ≫ g) pcr,
calc h   = 𝟙 a ≫ h : by hsimp
     ... = (i.hom ≫ i.ih.inv) ≫ h : by rwr <- i.ih.l_inv
     ... = i.hom ≫ (i.ih.inv ≫ h) : by hsimp
     ... = i.hom ≫ g : by rwr pcr   

@[hott, hsimp]
def iso_inv_move_rl {C : Type u} [is_precat.{v} C] {a b c : C} (i : a ≅ b)
  (g : c ⟶ a) (h : c ⟶ b) : h ≫ i.ih.inv = g -> h = g ≫ i.hom :=
assume pcl,
have (h ≫ i.ih.inv) ≫ i.hom = g ≫ i.hom, from 
  ap (λ g : c ⟶ a, g ≫ i.hom) pcl,
calc h   = h ≫ 𝟙 b : by hsimp
     ... = h ≫ (i.ih.inv ≫ i.hom) : by rwr <-i.ih.r_inv
     ... = (h ≫ i.ih.inv) ≫ i.hom : by hsimp
     ... = g ≫ i.hom : by rwr pcl 

/- Isomorphisms are uniquely determined by their underlying homomorphism:
   The inverse map by functorial equalities, and the functorial equalities 
   because the types of homomorphisms are sets. 
   
   As a consequence, isomorphisms between two given objects are also sets. -/
@[hott]
def hom_eq_to_iso_eq {C : Type u} [is_precat.{v} C] {a b : C} {i j : a ≅ b} :
  i.hom = j.hom -> i = j :=
begin
  hinduction i, hinduction j,
  intro hom_eq, fapply apd011 iso.mk, 
  exact hom_eq, apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott]
def iso_eq_eqv_hom_eq {C : Type u} [is_precat.{v} C] {a b : C} {i j : a ≅ b} :
  (i = j) ≃ i.hom = j.hom :=
begin
  fapply equiv.mk, exact ap iso.hom, 
  fapply adjointify, exact hom_eq_to_iso_eq, 
  { intro h, hinduction i, hinduction j, 
    change ap _ (apd011 _ _ _) = h, rwr ap_apd011 iso.mk _ _ iso.hom (λ a b, idp), 
    rwr idp_con },
  { intro i_eq, hinduction i_eq, rwr ap_idp, hinduction i, 
    change apd011 iso.mk idp (pathover_of_tr_eq (is_prop.elim ih ih)) = _, hsimp,
    change apd011 iso.mk idp idpo = _, rwr apd011_idp_idpo },
end

@[hott, instance]
def iso_is_set {C : Type u} [is_precat.{v} C] (a b : C) : is_set (a ≅ b) :=
begin
  apply is_trunc_succ_intro, intros i j,
  apply @is_trunc_equiv_closed_rev _ _ -1 iso_eq_eqv_hom_eq, apply_instance
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
  by refl

@[hott]
def id_inv_iso_inv {C : Type u} [is_precat.{v} C] {c₁ c₂ : C} (p : c₁ = c₂) :
  idtoiso p⁻¹ = inv_iso (idtoiso p) := 
begin hinduction p, refl end 

@[hott]
def id_inv_iso_inv_hom {C : Type u} [is_precat.{v} C] {c₁ c₂ : C} (p : c₁ = c₂) :
  (idtoiso p⁻¹).hom = (idtoiso p).ih.inv := 
begin hinduction p, refl end

@[hott]
def idtoiso_comp_eq {C : Type u} [is_precat.{v} C] {c₁ c₂ c₃ : C} 
  (p : c₁ = c₂) (q : c₂ = c₃) : 
  (idtoiso p).hom ≫ (idtoiso q).hom = (idtoiso (p ⬝ q)).hom :=
begin hinduction p, hinduction q, hsimp end   

/- Isomorphisms compose to isomorphisms. -/
@[hott]
def iso_comp {C : Type u} [is_precat.{v} C] {c₁ c₂ c₃ : C} :  
  (c₁ ≅ c₂) -> (c₂ ≅ c₃) -> (c₁ ≅ c₃) :=
begin 
  intros f g, fapply iso.mk, exact f.hom ≫ g.hom,
  fapply is_iso.mk,
  { exact g.ih.inv ≫ f.ih.inv },
  { rwr is_precat.assoc, rwr <- is_precat.assoc _ f.hom, 
    rwr f.ih.r_inv, rwr is_precat.id_comp, rwr g.ih.r_inv },
  { rwr is_precat.assoc, rwr <- is_precat.assoc g.hom, 
    rwr g.ih.l_inv, rwr is_precat.id_comp, rwr f.ih.l_inv }
end

@[hott]
def iso_comp_is_iso {C : Type u} [is_precat.{v} C] {c₁ c₂ c₃ : C} :  
  ∀ (f : c₁ ≅ c₂) (g : c₂ ≅ c₃), is_iso (f.hom ≫ g.hom) :=
λ f g, (iso_comp f g).ih

@[hott]
def iso_comp_snd_is_iso {C : Type u} [is_precat.{v} C] {c₁ c₂ c₃ : C} :  
  ∀ {f : c₁ ⟶ c₃} {g : c₁ ⟶ c₂} {h : c₂ ⟶ c₃}, is_iso f -> is_iso g -> f = g ≫ h -> is_iso h :=
begin
  intros f g h f_iso g_iso comp, 
  have q : h = (iso.mk g g_iso).ih.inv ≫ f, from 
    begin fapply iso_move_lr, exact comp⁻¹ end,
  rwr q, fapply iso_comp_is_iso (iso.mk g_iso.inv _) (iso.mk f f_iso), exact (inv_iso (iso.mk g g_iso)).ih
end 

@[hott]
def id_iso_comp_iso {C : Type u} [is_precat.{v} C] {c₁ c₂ : C} : 
  Π {f : c₁ ⟶ c₂} (g : c₂ ⟶ c₁), is_iso f -> 𝟙 c₁ = f ≫ g -> is_iso g :=
begin
  intros f g f_iso comp, fapply @iso_comp_snd_is_iso _ _ _ _ _ (𝟙 c₁) f _ _ f_iso comp, exact (id_iso c₁).ih
end

/- `idtoiso` commutes with functors -/
@[hott]
def funct_idtoiso {C : Type _} [is_precat C] {c₁ c₂ : C} 
  {D : Type _} [is_precat D] (F : C ⥤ D) (p : c₁ = c₂) :
  F.map (idtoiso p).hom = (idtoiso (ap F.obj p)).hom :=
begin 
  hinduction p, rwr idtoiso_refl_eq, rwr ap_idp, 
  rwr idtoiso_refl_eq, change F.map (𝟙 c₁) = _, rwr F.map_id 
end  

/- Functors map isomorphisms to isomorphisms. -/
@[hott]
def funct_iso_iso {C : Type _} [is_precat C] {c₁ c₂ : C} 
  {D : Type _} [is_precat D] (F : C ⥤ D) : c₁ ≅ c₂ -> (F.obj c₁ ≅ F.obj c₂) :=
begin
  intro i, fapply iso.mk, 
  { exact F.map i.hom },
  { fapply is_iso.mk, 
    { exact F.map i.ih.inv },
    { rwr <- F.map_comp, rwr i.ih.r_inv, rwr F.map_id },
    { rwr <- F.map_comp, rwr i.ih.l_inv, rwr F.map_id } }
end

/- Homomorphisms mapped by fully faithful functors to isomorphisms are isomorphisms. -/
@[hott, reducible]
def ff_functor_iso_iso {C : Type u} [is_precat C] {D : Type u'} 
  [is_precat D] {F : C ⥤ D} (ffF : is_fully_faithful_functor F) :
  Π {x y : C} (f : x ⟶ y), is_iso (F.map f) -> is_iso f :=
begin 
  intros x y f iso_Ff, fapply is_iso.mk,
  { exact (inv_of_bijection (bijection.mk _ (@ffF y x))).1 iso_Ff.inv },
  { apply (@ffF y y).inj, rwr functor.map_comp, rwr functor.map_id, 
    change (bijection.mk _ (@ffF y x)) _ ≫ _ = _,
    rwr (inv_of_bijection (bijection.mk _ (@ffF y x))).2.r_inv, exact iso_Ff.r_inv },
  { apply (@ffF x x).inj, rwr functor.map_comp, rwr functor.map_id, 
    change _ ≫ (bijection.mk _ (@ffF y x)) _ = _,
    rwr (inv_of_bijection (bijection.mk _ (@ffF y x))).2.r_inv, exact iso_Ff.l_inv }
end

@[hott]
def funct_id_iso_id_iso {C : Type _} [is_precat C] {D : Type _} [is_precat D] 
  (F : C ⥤ D) : Π {c : C}, funct_iso_iso F (id_iso c) = id_iso (F.obj c) :=
begin
  intro c, apply hom_eq_to_iso_eq, change F.map (𝟙 _) = _, rwr functor.map_id
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

@[hott]
def functor_eq_to_nat_trans {A : Type _} [is_precat A] {B : Type _} 
  [is_precat B] {F G : A ⥤ B} : (F = G) -> (F ⟹ G) :=
begin 
  intro p, fapply nat_trans.mk,
  { intro a, exact (idtoiso (ap (λ H : A ⥤ B, H.obj a) p)).hom },
  { intros a a' f, hinduction p, change _ ≫ 𝟙 _ = 𝟙 _ ≫ _, rwr is_precat.id_comp, rwr is_precat.comp_id } 
end

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

@[hott]
def category.isotoid {C : Type _} [is_cat C] : 
  Π {a b : C}, a ≅ b -> a = b :=
assume a b iso,  
@is_equiv.inv _ _ _ (is_cat.ideqviso a b) iso  

@[hott, hsimp]
def category.ideqviso {C : Type _} [is_cat C] : 
  Π {a b : C}, (a = b) ≃ (a ≅ b) :=
λ a b, equiv.mk idtoiso (is_cat.ideqviso a b)

@[hott, hsimp]
def category.idtoiso_rinv {C : Type _} [is_cat C] {a b : C} :
  ∀ i : a ≅ b, idtoiso (idtoiso⁻¹ᶠ i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_linv {C : Type _} [is_cat C] {a b : C} :
  ∀ p : a = b, idtoiso⁻¹ᶠ (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_rinv' {C : Type _} [is_cat C] {a b : C} :
  ∀ i : a ≅ b, idtoiso (category.isotoid i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_linv' {C : Type _} [is_cat C] {a b : C} :
  ∀ p : a = b, category.isotoid (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b)

@[hott]
def isotoid_id_refl {C : Type _} [is_cat C] :
  Π (a : C), category.isotoid (id_iso a) = refl a :=
begin intro a, exact category.idtoiso_linv' (refl a) end 

@[hott]
def iso_hom_tr_comp {C : Type _} [is_cat C] {c₁ c₂ d : C} (i : c₁ ≅ c₂)
  (h : c₁ ⟶ d) : (idtoiso⁻¹ᶠ i) ▸ h = i⁻¹ʰ.hom ≫ h :=
begin 
  rwr <- (category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp (idtoiso⁻¹ᶠ i) h
end 

@[hott]
def iso_hom_tr_comp' {C : Type _} [is_cat C] {c d₁ d₂ : C} (i : d₁ ≅ d₂)
  (h : c ⟶ d₁) : (idtoiso⁻¹ᶠ i) ▸ h = h ≫ i.hom :=
begin 
  rwr <- (category.idtoiso_rinv i),  
  rwr category.idtoiso_linv (idtoiso⁻¹ᶠ i),
  exact id_hom_tr_comp' (idtoiso⁻¹ᶠ i) h
end

@[hott]
def idtoiso_is_inj {C : Type _} [is_cat C] {c₁ c₂ : C} {p q : c₁ = c₂} :
  idtoiso p = idtoiso q -> p = q :=
begin 
  intro r, rwr <- (category.idtoiso_linv p), rwr <- (category.idtoiso_linv q), 
  apply ap idtoiso⁻¹ᶠ, exact r
end

/- In categories, identity types are sets. In categories whose objects form a set, 
   isomorphism types are propositions (since identity types are propositions). -/
@[hott, instance]
def cat_eq_is_set {C : Type _} [is_cat C] {c₁ c₂ : C} : is_set (c₁ = c₂) :=
  is_trunc_equiv_closed_rev 0 category.ideqviso (iso_is_set c₁ c₂)

@[hott, instance]
def cat_set_eq_is_prop {C : Type _} [is_set C] [H : is_cat C] {c₁ c₂ : C} : is_prop (c₁ ≅ c₂) :=
  is_trunc_equiv_closed -1 (@category.ideqviso C H _ _) (is_trunc_eq -1 _ _)

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


/- Induction on isomorphisms via equalities, with elimination rule -/
@[hott]
def iso_ind_of_eq {A : Type _} [is_cat A] {D : Π {a b : A} (i : a ≅ b), Type _} :
  (Π {a b : A} (p : a = b), D (idtoiso p)) -> Π {a b : A} (i : a ≅ b), D i :=
assume Hp a b i, category.idtoiso_rinv i ▸ Hp (idtoiso⁻¹ᶠ i)

@[hott]
def iso_ind {A : Type _} [is_cat A] {D : Π {a b : A} (i : a ≅ b), Type _} :
  (Π (a : A), D (id_iso a)) -> Π {a b : A} (i : a ≅ b), D i :=
begin intros Hid, apply iso_ind_of_eq, intros a b p, hinduction p, exact Hid a end

@[hott]
def iso_ind_id {A : Type _} [is_cat A] {D : Π {a b : A} (i : a ≅ b), Type _} 
  (Hid : Π (a : A), D (id_iso a)) : Π (a : A), iso_ind Hid (id_iso a) = Hid a :=
begin
  intro a, 
  change category.idtoiso_rinv (idtoiso (refl a)) ▸[λ i : a ≅ a, D i] 
           @eq.rec _ _ (λ (b : A) (p : a = b), D (idtoiso p)) 
                       (Hid a) a (category.isotoid (id_iso a)) = 
           @eq.rec _ _ (λ (b : A) (p : a = b), D (idtoiso p)) 
                       (Hid a) a (refl a), 
  let p := @pathover_ap _ _ _ _ D idtoiso (isotoid_id_refl a) _ _ 
              (apd (@eq.rec _ _ (λ (b : A) (p : a = b), D (idtoiso p)) 
                                             (Hid a) a) (isotoid_id_refl a)),
  rwr <- tr_eq_of_pathover p, 
  change @is_equiv.right_inv _ _ idtoiso (is_cat.ideqviso _ _) _ ▸ _ = _,
  rwr (is_cat.ideqviso _ _).adj
end 

/- The underlying functor of an isomorphism between two precategories as encoded by
   `precat_iso` has an inverse, in the sense that its compositions with the functor
   are naturally isomorphic to the respective identity functors. In the [Hott-Book], this 
   is actually called an equivalence of precategories if an additional adjointness 
   condition is satisfied that makes the notion unique. It follows from 
   `precat_iso` by [Lem.9.4.15] (that is, `precat_id_equiv_iso` in [categories.precat]) 
   and induction on identity. 
   
   However, the equivalence of isomorphisms with equalities of precategories requires them 
   to be in the same universe. This is too restrictive in some cases, so we make the
   definition of an equivalence of precategories more explicit by fixing the 
   components of the natural transformations to applications of `idtoiso` and construct 
   such equivalences of two precategories directly from their isomorphisms. This uses 
   ideas from the proof of [Lem.9.4.5] in the [HoTT-Book].     -/
@[hott]
structure precat_equiv (C D : Type _) [is_precat C] [is_precat D] :=
  (functor : C ⥤ D)
  (inv_functor : D ⥤ C)
  (rinv_obj : (inv_functor ⋙ functor).obj = (id_functor D).obj)
  (rinv_map : Π {d₁ d₂ : D} (h : d₁ ⟶ d₂), (inv_functor ⋙ functor).map h = 
            (idtoiso (ap10 rinv_obj d₁)).hom ≫ h ≫ (idtoiso (ap10 rinv_obj d₂)⁻¹).hom)
  (linv_obj : (functor ⋙ inv_functor).obj = (id_functor C).obj)
  (linv_map : Π {c₁ c₂ : C} (h : c₁ ⟶ c₂), (functor ⋙ inv_functor).map h = 
            (idtoiso (ap10 linv_obj c₁)).hom ≫ h ≫ (idtoiso (ap10 linv_obj c₂)⁻¹).hom)

@[hott]
def precat_equiv_idp (C : Type _) [is_precat C] : precat_equiv C C :=
begin
  fapply precat_equiv.mk,
    exact id_functor C, exact id_functor C, 
    exact ap functor.obj (funct_id_comp _),
    { intros c₁ c₂ h, 
      change h = (idtoiso (ap10 (ap functor.obj (functor_eq (idpath 
                                               (id_functor C).obj) _)) c₁)).hom ≫ _ ≫ 
                 (idtoiso (ap10 (ap functor.obj (functor_eq (idpath 
                                               (id_functor C).obj) _)) c₂)⁻¹).hom, 
      rwr functor_eq_obj, change h = (idtoiso idp).hom ≫ _ ≫ (idtoiso idp).hom, 
      rwr idtoiso_refl_eq, rwr idtoiso_refl_eq, change h = 𝟙 c₁ ≫ _ ≫ 𝟙 c₂, 
      rwr is_precat.comp_id, rwr is_precat.id_comp }, 
    exact ap functor.obj (funct_id_comp _),
    { intros c₁ c₂ h, 
      change h = (idtoiso (ap10 (ap functor.obj (functor_eq (idpath 
                                               (id_functor C).obj) _)) c₁)).hom ≫ _ ≫ 
                 (idtoiso (ap10 (ap functor.obj (functor_eq (idpath 
                                               (id_functor C).obj) _)) c₂)⁻¹).hom, 
      rwr functor_eq_obj, change h = (idtoiso idp).hom ≫ _ ≫ (idtoiso idp).hom, 
      rwr idtoiso_refl_eq, rwr idtoiso_refl_eq, change h = 𝟙 c₁ ≫ _ ≫ 𝟙 c₂, 
      rwr is_precat.comp_id, rwr is_precat.id_comp }
end

@[hott]
def precat_iso_to_inv_functor {C D : Type _} [is_precat C] [is_precat D] :
  precat_iso C D -> D ⥤ C :=
begin
  intro pci, fapply precategories.functor.mk,
  { exact pci.equiv.inv },
  { intros d₁ d₂ h, 
    fapply (inv_bijection_of (bijection.mk _ (@precat_iso.ff _ _ _ _ pci _ _))).map,
    exact (idtoiso (@is_equiv.right_inv _ _ _ pci.equiv d₁)).hom ≫ h ≫ 
          (idtoiso (@is_equiv.right_inv _ _ _ pci.equiv d₂)⁻¹).hom },
  { intro d, change (inv_bijection_of _).map (_ ≫ (𝟙 d) ≫ _) = _, rwr is_precat.id_comp,
    rwr idtoiso_comp_eq, rwr con.right_inv, apply eq.inverse,
    apply bijection_l_to_r, change pci.functor.map _ = _, rwr functor.map_id },
  { intros x y z f g, change (inv_bijection_of _).map _ = (inv_bijection_of _).map _ ≫ 
                                                          (inv_bijection_of _).map _, 
    apply eq.inverse, apply bijection_l_to_r, change pci.functor.map _ = _,
    rwr functor.map_comp pci.functor, 
    change (bijection.mk _ (@precat_iso.ff _ _ _ _ pci _ _)).map _ ≫ 
           (bijection.mk _ (@precat_iso.ff _ _ _ _ pci _ _)).map _ = _, 
    rwr inv_bij_r_inv, rwr inv_bij_r_inv, rwr is_precat.assoc, rwr is_precat.assoc f, 
    rwr <- is_precat.assoc _ _ (g ≫ _), rwr idtoiso_comp_eq, rwr con.left_inv,
    rwr idtoiso_refl_eq, change _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ _ = _, rwr is_precat.id_comp, 
    rwr is_precat.assoc f g }
end

@[hott]
def precat_iso_to_equiv {C D : Type _} [is_precat C] [is_precat D] :
  precat_iso C D -> precat_equiv C D :=
begin
  intro pci, fapply precat_equiv.mk,
  { exact pci.functor },
  { exact precat_iso_to_inv_functor pci },
  { apply eq_of_homotopy, intro d, 
    exact @is_equiv.right_inv _ _ pci.functor.obj (precat_iso.equiv pci) d },
  { intros d₁ d₂ h, rwr ap10_eq_of_homotopy, 
    change (bijection.mk _ (@precat_iso.ff _ _ _ _ pci _ _)).map 
                                            ((inv_bijection_of _).map _) = _, 
    rwr inv_bij_r_inv },
  { apply eq_of_homotopy, intro c, 
    exact @is_equiv.left_inv _ _ pci.functor.obj (precat_iso.equiv pci) c },
  { intros d₁ d₂ h, rwr ap10_eq_of_homotopy, 
    change (inv_bijection_of _).map _ = _, apply eq.inverse, apply bijection_l_to_r,
    change pci.functor.map _ = _, rwr pci.functor.map_comp, rwr pci.functor.map_comp,
    rwr funct_idtoiso, rwr funct_idtoiso, rwr is_equiv.adj, rwr is_equiv.adj, rwr ap_inv }
end

@[hott]
def precat_iso_to_equiv_obj (C : Type _) [pcC : is_precat C] (D : Type _) 
  [pcD : is_precat D] {pci : precat_iso C D} :
  functor.obj (precat_equiv.inv_functor (precat_iso_to_equiv pci)) = 
                                          @is_equiv.inv _ _ pci.functor.obj pci.equiv :=
idp

/- Isomorphic precategories both have a category structure, or none. We prove a version 
   that does not require the precategories to be in the same category, via the same 
   statement assuming that the precategories are equivalent. -/
@[hott]
def precat_equiv_cat_cat {C D : Type _} [HC : is_cat C] [HD : is_precat D] :
  precat_equiv C D -> is_cat D :=
begin
  intro pce, fapply is_cat.mk, intros d₁ d₂, fapply adjointify,
  { intro i, 
    apply λ p, (ap10 (precat_equiv.rinv_obj pce) d₁)⁻¹ ⬝ p ⬝ 
               (ap10 (precat_equiv.rinv_obj pce) d₂),
    apply ap pce.functor.obj, apply category.isotoid, 
    exact funct_iso_iso pce.inv_functor i },
  { intro i, apply hom_eq_to_iso_eq, rwr <- idtoiso_comp_eq, rwr <- idtoiso_comp_eq,
    rwr <- funct_idtoiso, rwr category.idtoiso_rinv', apply eq.inverse,
    apply iso_inv_move_rl, apply iso_inv_move_lr, 
    rwr <- id_inv_iso_inv_hom, rwr hott.eq.inv_inv, rwr <- id_inv_iso_inv_hom, 
    change _ = pce.functor.map (pce.inv_functor.map i.hom),
    apply eq.inverse, apply pce.rinv_map },
  { intro i, hinduction i, rwr idtoiso_refl_eq, rwr funct_id_iso_id_iso, 
    rwr isotoid_id_refl, rwr ap_idp, change _ ⬝ _ ⬝ _ = _, rwr con_idp, 
    rwr con.left_inv }
end 

@[hott]
def precat_iso_cat_cat (C D : Type _) [HC : is_cat C] [HD : is_precat D] :
  precat_iso C D -> is_cat D :=
λ pci, precat_equiv_cat_cat (precat_iso_to_equiv pci)

end categories

end hott