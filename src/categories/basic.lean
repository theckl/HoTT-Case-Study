import sets.algebra init2 types2 sets.axioms

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
structure is_iso {C : Type u} [precategory.{v} C] {a b : C} (f : a ⟶ b) :=
  (inv : b ⟶ a)
  (r_inv : inv ≫ f = 𝟙 b)
  (l_inv : f ≫ inv = 𝟙 a)

@[hott]
def is_iso_to_iso {C : Type u} [precategory.{v} C] {a b : C} (f : a ⟶ b) 
  (H : is_iso f) : a ≅ b := iso.mk f H.inv H.r_inv H.l_inv

@[hott]
def iso_to_is_iso {C : Type u} [precategory.{v} C] {a b : C} (f : a ≅ b) : 
  is_iso f.hom := is_iso.mk f.inv f.r_inv f.l_inv  

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
  begin intro eq, exact eq ▸[λ c, a ≅ c] id_is_iso a end

/- `idtoiso` is natural. -/
@[hott, hsimp]
def idtoiso_refl_eq {C : Type u} [precategory.{v} C] (a : C) : idtoiso (refl a) = id_is_iso a :=
  by hsimp

@[hott]
def id_inv_iso_inv {C : Type u} [precategory.{v} C] {c₁ c₂ : C} (p : c₁ = c₂) :
  idtoiso p⁻¹ = inv_iso (idtoiso p) := 
begin hinduction p, refl end 

/- The next two facts correspond to [HoTT-Book, Lem.9.1.9]. -/
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

@[hott, hsimp]
def category.idtoiso_rinv' {obj : Type u} [category.{v} obj] {a b : obj} :
  ∀ i : a ≅ b, idtoiso (category.isotoid i) = i :=
is_equiv.right_inv (@idtoiso _ _ a b) 

@[hott, hsimp]
def category.idtoiso_linv' {obj : Type u} [category.{v} obj] {a b : obj} :
  ∀ p : a = b, category.isotoid (idtoiso p) = p :=
is_equiv.left_inv (@idtoiso _ _ a b) 

@[hott]
def isotoid_id_refl {obj : Type u} [category.{v} obj] :
  Π (a : obj), category.isotoid (id_is_iso a) = refl a :=
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


/- In a category `C` we can define a subobject of an object `c` as a monomorphism `a ⟶ c`. Two 
   such subobjects are equal if and only if there is an isomorphism between the sources of the 
   monomorphisms factorizing the monomorphisms. Therefore in HoTT categories, it is not necessary 
   to define subobjects as isomorphism classes. -/
@[hott]
def is_mono {C : Type u} [category.{v} C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) :=
  Π (d : C) (g₁ g₂ : d ⟶ c₁), g₁ ≫ f = g₂ ≫ f -> g₁ = g₂

@[hott, instance]
def is_mono_is_prop {C : Type u} [category.{v} C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) : 
  is_prop (is_mono f) :=
begin apply is_prop_dprod, intro d, apply_instance end 

@[hott]
def isos_are_mono {C : Type u} [category.{v} C] {c₁ c₂ : C} (i : c₁ ≅ c₂) : is_mono i.hom :=  
  assume d g₁ g₂ eq_comp, 
  calc g₁ = g₁ ≫ 𝟙 c₁ : by rwr precategory.comp_id
       ... = g₁ ≫ (i.hom ≫ i.inv) : by rwr iso.l_inv
       ... = (g₁ ≫ i.hom) ≫ i.inv : by rwr precategory.assoc
       ... = (g₂ ≫ i.hom) ≫ i.inv : by rwr eq_comp
       ... = g₂ : by rwr precategory.assoc; rwr iso.l_inv; rwr precategory.comp_id   

@[hott]
structure hom_of_monos {C : Type u} [category.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} 
  (Hf : is_mono f) {g : d₂ ⟶ c} (Hg : is_mono g) :=
(hom_obj : d₁ ⟶ d₂)
(fac : hom_obj ≫ g = f)

@[hott, instance]
def is_prop_hom_of_monos {C : Type u} [category.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : is_prop (hom_of_monos Hf Hg) :=
begin 
  apply is_prop.mk, intros hm₁ hm₂, hinduction hm₁ with h₁ fac₁, hinduction hm₂ with h₂ fac₂, 
  fapply apd011 (hom_of_monos.mk Hf Hg), 
  { apply Hg, exact fac₁ ⬝ fac₂⁻¹ },
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end  

@[hott]
structure iso_of_monos {C : Type u} [category.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) :=
(iso_obj : d₁ ≅ d₂)
(fac : iso_obj.hom ≫ g = f) 

@[hott]
def iso_of_monos_eq {C : Type u} [category.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} {Hf : is_mono f}
  {g : d₂ ⟶ c} {Hg : is_mono g} (im₁ im₂ : iso_of_monos Hf Hg) : 
  im₁.iso_obj = im₂.iso_obj -> im₁ = im₂ :=
begin 
  hinduction im₁ with iso_obj₁ fac₁, hinduction im₂ with iso_obj₂ fac₂, hsimp, 
  intro p, fapply apd011 (iso_of_monos.mk Hf Hg), assumption,
  apply pathover_of_tr_eq, exact is_set.elim _ _ 
end 

@[hott]
def homs_eqv_iso_of_monos {C : Type u} [category.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : 
  (hom_of_monos Hf Hg) × (hom_of_monos Hg Hf) ≃ iso_of_monos Hf Hg :=
begin 
  fapply equiv.mk, 
  { intro homs, let sh₁ := homs.1, let sh₂ := homs.2, fapply iso_of_monos.mk, 
    { fapply iso.mk, 
      { exact sh₁.hom_obj },
      { exact sh₂.hom_obj },
      { apply Hg d₂ (sh₂.hom_obj ≫ sh₁.hom_obj) (𝟙 d₂), rwr precategory.assoc, 
        rwr sh₁.fac, rwr sh₂.fac, hsimp },
      { apply Hf d₁ (sh₁.hom_obj ≫ sh₂.hom_obj) (𝟙 d₁), rwr precategory.assoc, 
        rwr sh₂.fac, rwr sh₁.fac, hsimp } },
    { hsimp, rwr sh₁.fac } },
  { fapply adjointify, 
    { intro i, fapply pair, 
      { fapply hom_of_monos.mk, exact i.iso_obj.hom, exact i.fac },
      { fapply hom_of_monos.mk, exact i.iso_obj.inv, rwr iso_move_lr _ _ _ i.fac } },
    { intro im, hinduction im with i fac, apply iso_of_monos_eq _ _, 
      { apply hom_eq_to_iso_eq, hsimp } },
    { intro hm, hinduction hm with hm₁ hm₂, 
      hinduction hm₁ with hom_obj₁ fac₁, hinduction hm₂ with hom_obj₂ fac₂, fapply prod.prod_eq,
      { fapply apd011 (hom_of_monos.mk Hf Hg), hsimp, 
        apply pathover_of_tr_eq, exact is_set.elim _ _ },
      { fapply apd011 (hom_of_monos.mk Hg Hf), hsimp, 
        apply pathover_of_tr_eq, exact is_set.elim _ _ } } }
end  

@[hott, instance]
def is_prop_iso_of_monos {C : Type u} [category.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : is_prop (iso_of_monos Hf Hg) :=
begin apply is_trunc_equiv_closed -1 (homs_eqv_iso_of_monos Hf Hg), apply_instance end

@[hott]
structure subobject {C : Type u} [category.{v} C] (c : C) :=
  (obj : C)
  (hom : obj ⟶ c)
  (is_mono : is_mono hom)  

@[hott]
def subobject_eta {C : Type u} [category.{v} C] {c : C} (so : subobject c) :
  so = subobject.mk so.obj so.hom so.is_mono :=
begin hinduction so, refl end   

@[hott]
def subobject_eta_eq {C : Type u} [category.{v} C] {c : C} (obj : C) (hom : obj ⟶ c) 
  (is_mono : is_mono hom) : subobject_eta (subobject.mk obj hom is_mono) = idp :=
rfl  

@[hott] 
def subobject_eq_idp {C : Type u} [category.{v} C] {c : C} {s : subobject c} 
  (p : s.obj = s.obj) (q : s.hom =[p; λ d, d ⟶ c] s.hom) 
  (r : s.is_mono =[apd011 (λ (a : C) (b : ↥(a ⟶ c)), is_mono b) p q; id] s.is_mono) :
  p = idp -> apd0111 subobject.mk p q r = idp :=
begin 
  intro Hp, 
  have Hq : q =[Hp; λ p' : s.obj = s.obj, s.hom =[p'; λ d, d ⟶ c] s.hom] idpatho s.hom, from 
    begin apply pathover_of_tr_eq, exact set_po_eq _ _ end,
  have H : is_prop (s.is_mono =[idp; id] s.is_mono), from 
    begin 
      apply is_trunc_equiv_closed_rev -1 (pathover_equiv_tr_eq _ _ _), exact is_trunc_eq -1 _ _
     end,  
  have Hr : r =[apd011 (λ (x : s.obj = s.obj) (y : s.hom =[x; λ d, d ⟶ c] s.hom), 
                          apd011 (λ (obj : C) (hom : obj ⟶ c), is_mono hom) x y) Hp Hq;
                λ Hf : is_mono s.hom = is_mono s.hom, s.is_mono =[Hf; id] s.is_mono] 
                                                                      idpatho s.is_mono, from 
    begin apply pathover_of_tr_eq, exact @is_prop.elim _ H _ _ end, 
  rwr @apd0111_eq _ _ _ (λ (obj : C) (hom : obj ⟶ c), is_mono hom) _ _ _ _ _ _ _ _ _ _ _ _ _ 
                                                                                       Hp Hq Hr 
end   

/- A homomorphism between subobjects compatible with the injections is itself injection. Hence,
   homomorphisms between subobjects in both ways imply an isomorphism of subobjects and therefore
   equality. -/
@[hott]
def subobject_hom {C : Type u} [category.{v} C] {c : C} (s₁ s₂ : subobject c) :=
  hom_of_monos s₁.is_mono s₂.is_mono

@[hott, instance]
def subobject_hom_is_prop {C : Type u} [category.{v} C] {c : C} (s₁ s₂ : subobject c) :
  is_prop (subobject_hom s₁ s₂) :=
begin change is_prop (hom_of_monos s₁.is_mono s₂.is_mono), apply_instance end    

@[hott]
def equal_subobj_to_iso_mono {C : Type u} [category.{v} C] {c : C} (s₁ s₂ : subobject c) :
  s₁ = s₂ -> iso_of_monos s₁.is_mono s₂.is_mono :=
begin 
  intro p, fapply iso_of_monos.mk, 
  exact (idtoiso (ap subobject.obj p)), 
  hinduction p, hsimp 
end  

@[hott] 
def idp_subobj_to_iso_mono {C : Type u} [category.{v} C] {c : C} (s : subobject c) :
  equal_subobj_to_iso_mono s s idp = iso_of_monos.mk s.is_mono s.is_mono (id_is_iso s.obj) 
                                                     (precategory.id_comp s.hom) :=
begin apply iso_of_monos_eq, change idtoiso idp = id_is_iso s.obj, rwr idtoiso_refl_eq end                                                     

@[hott]
def iso_mono_to_equal_subobj {C : Type u} [category.{v} C] {c : C} (s₁ s₂ : subobject c) :
  iso_of_monos s₁.is_mono s₂.is_mono -> s₁ = s₂ :=
assume im, (subobject_eta s₁) ⬝  
begin 
  fapply apd0111 subobject.mk, 
  { exact category.isotoid im.iso_obj },
  { apply pathover_of_tr_eq, 
    change idtoiso⁻¹ᶠ im.iso_obj ▸[λ (d : C), ↥(d ⟶ c)] s₁.hom = s₂.hom, 
    rwr iso_hom_tr_comp, 
    calc (im.iso_obj)⁻¹ʰ ≫ s₁.hom = (im.iso_obj)⁻¹ʰ ≫ im.iso_obj.hom ≫ s₂.hom : 
                                                                           by rwr im.fac
         ... = ((im.iso_obj)⁻¹ʰ ≫ im.iso_obj.hom) ≫ s₂.hom : by rwr precategory.assoc
         ... = 𝟙 s₂.obj ≫ s₂.hom : by rwr iso.r_inv 
         ... = s₂.hom : by rwr precategory.id_comp },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros d g₁ g₂, 
    apply eq_of_homotopy, intro comp_eq, exact is_prop.elim _ _ } 
end 
⬝ (subobject_eta s₂)⁻¹  

@[hott]
def iso_mono_to_equal_subobj_iso {C : Type u} [category.{v} C] {c : C} {s₁ s₂ : subobject c} 
  (im : iso_of_monos s₁.is_mono s₂.is_mono) : 
  ap subobject.obj (iso_mono_to_equal_subobj s₁ s₂ im) = category.isotoid im.iso_obj :=
begin
  hinduction s₁ with obj₁ hom₁ is_mono₁, hinduction s₂ with obj₂ hom₂ is_mono₂,
  change ap subobject.obj ((subobject_eta _) ⬝ (apd0111 subobject.mk _ _ _) ⬝ _) = _, 
  rwr subobject_eta_eq, rwr subobject_eta_eq, rwr idp_con, rwr idp_inv, rwr con_idp,
  let HP : Π (obj : C) (hom : obj ⟶ c) (is_mono : is_mono hom), 
                                     subobject.obj (subobject.mk obj hom is_mono) = obj := 
      begin intros obj hom is_mono, exact idp end, 
  rwr ap_apd0111 subobject.mk _ _ _ subobject.obj HP, 
  change idp ⬝ category.isotoid im.iso_obj ⬝ idp⁻¹ = _, rwr idp_con   
end    

@[hott]
def equal_subobj_eqv_iso_mono {C : Type u} [category.{v} C] {c : C} (s₁ s₂ : subobject c) :
  s₁ = s₂ ≃ iso_of_monos s₁.is_mono s₂.is_mono :=
begin
  fapply equiv.mk,
  { exact equal_subobj_to_iso_mono s₁ s₂ },
  { fapply adjointify,
    { exact iso_mono_to_equal_subobj s₁ s₂ },
    { hinduction s₁ with obj₁ hom₁ is_mono₁, hinduction s₂ with obj₂ hom₂ is_mono₂,
      intro im, hinduction im with iso_obj fac, apply iso_of_monos_eq _ _, hsimp,
      change idtoiso (ap subobject.obj _) = _, rwr iso_mono_to_equal_subobj_iso,
      change idtoiso (idtoiso⁻¹ᶠ _) = _, rwr category.idtoiso_rinv },
    { intro p, hinduction p, --hinduction s₁ with obj₁ hom₁ is_mono₁, 
      rwr idp_subobj_to_iso_mono, 
      change (subobject_eta _) ⬝ (apd0111 subobject.mk (category.isotoid (id_is_iso s₁.obj)) _ _) ⬝ 
                                                                                              _ = _, 
      apply con_eq_of_eq_con_inv, apply con_eq_of_eq_inv_con, rwr idp_con, 
      rwr con.right_inv, apply subobject_eq_idp, rwr isotoid_id_refl } }
end    

/- The subobjects of an object in a HoTT-category form a set, so a HoTT-category is well-powered. -/
@[hott, instance]
def subobject_is_set {C : Type u} [category.{v} C] {c : C} : is_set (subobject c) :=
begin 
  apply is_trunc_succ_intro, intros s₁ s₂, 
  apply is_trunc_equiv_closed_rev -1 (equal_subobj_eqv_iso_mono s₁ s₂), 
  apply is_trunc_equiv_closed -1 (homs_eqv_iso_of_monos s₁.is_mono s₂.is_mono), 
  apply_instance 
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
def functor_eta [precategory.{v} C] [precategory.{v'} D] (F : C ⥤ D) : 
  F = functor.mk F.obj F.map F.map_id F.map_comp :=
begin hinduction F, refl end 

@[hott]
def functor_eta_mk [precategory.{v} C] [precategory.{v'} D] :
  Π obj map map_id map_comp, functor_eta C D (functor.mk obj map map_id map_comp) = idp :=
assume obj map map_id map_comp, rfl  

@[hott]
def functor_mk_obj [precategory.{v} C] [precategory.{v'} D] :
  Π obj map map_id map_comp, @functor.obj C D _ _ (functor.mk obj map map_id map_comp) = obj :=
assume obj map map_id map_comp, rfl   

/- Functors are equal if their maps of objects and arrows are equal. -/
@[hott]
def functor_eq [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} :
  Π (p : F.obj = G.obj), 
    (F.map =[p; λ f : C -> D, Π (x y : C), (x ⟶ y) -> (f x ⟶ f y)] G.map) -> F = G :=
begin 
  intros p q, 
  exact (functor_eta C D F) ⬝ (apd01111_v2 functor.mk p q 
          (pathover_of_tr_eq (is_prop.elim _ _))  (pathover_of_tr_eq (is_prop.elim _ _)))
        ⬝ (functor_eta C D G)⁻¹  
end  

@[hott]
def functor_eq_idp' [precategory.{v} C] [precategory.{v'} D] {obj : C -> D} 
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
def functor_eq_idp [precategory.{v} C] [precategory.{v'} D] {F : C ⥤ D} :
  functor_eq C D (@idp _ F.obj) idpo = idp :=
begin hinduction F, rwr functor_eq_idp' end

@[hott]
def functor_eq_obj [precategory.{v} C] [precategory.{v'} D] {F G : C ⥤ D} :
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

@[hott, reducible]
def id_functor [precategory.{v} C] : C ⥤ C :=
  functor.mk (λ c : C, c) (λ c₁ c₂ f, f) (λ c, idp) (λ c₁ c₂ c₃ f g, idp)  


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
@[hott, reducible]
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

/- The fully embedded category of a type injectively mapped to a category. 
   We start with a synonym for an (embedded) type `D`, on which the category structure
   will be defined, as in [category_theory.full_subcategory] of the mathlib. -/
@[hott]
def ind_cat_type {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C) := D

@[hott, instance]
def mapped_type_has_hom {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C) : 
  has_hom (ind_cat_type f) :=
begin fapply has_hom.mk, intros d₁ d₂, exact f d₁ ⟶ f d₂ end  

@[hott]
def ind_type_hom_hom {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C)
  {d₁ d₂ : ind_cat_type f} : (d₁ ⟶ d₂) -> (f d₁ ⟶ f d₂) := 
assume h, h  

@[hott, instance]
def ind_type_cat_struct {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C) : 
  category_struct (ind_cat_type f) :=
begin
  fapply category_struct.mk,
  { intro a, exact 𝟙 (f a) },
  { intros a b c f g, exact f ≫ g }
end  

@[hott, instance]
def fully_ind_precategory {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C) : 
  precategory (ind_cat_type f) :=
begin
  fapply precategory.mk,
  { intros d₁ d₂ f, hsimp },
  { intros d₁ d₂ f, hsimp },
  { intros d₁ d₂ d₃ d₄ f g h, hsimp, refl }
end  

@[hott]
def ind_type_iso_iso {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C)
  {d₁ d₂ : ind_cat_type f} : (d₁ ≅ d₂) -> (f d₁ ≅ f d₂) := 
begin
  intro i, fapply iso.mk,  
  { exact i.hom },
  { exact i.inv },
  { exact i.r_inv },
  { exact i.l_inv }
end  

@[hott]
def ind_idtoiso_hom {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C)
  (inj : is_injective (λ d : ind_cat_type f, f d)) {d₁ d₂ : ind_cat_type f} : 
  Π p : f d₁ = f d₂, (idtoiso (inj_imp inj d₁ d₂ p)).hom = (idtoiso p).hom :=
begin 
  fapply equiv_arg_exchange,
  { exact d₁ = d₂ },
  { intro p, exact ap f p },
  { exact inj d₁ d₂ },
  { intro q, fapply @eq.rec _ d₁ (λ d₂, λ q : d₁ = d₂, 
               (idtoiso (inj_imp inj d₁ d₂ (ap f q))).hom = (idtoiso (ap f q)).hom), 
    change (idtoiso (inj_imp inj d₁ d₁ (ap f (refl d₁)))).hom = 𝟙 d₁, 
    have H : inj_imp inj d₁ d₁ (ap f (refl d₁)) = refl d₁, from
      @is_equiv.left_inv _ _ _ (inj d₁ d₁) (refl d₁), 
    rwr H }
end

@[hott, instance]
def fully_embedded_category {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C)
  [inj : is_injective f] : category (ind_cat_type f) :=
begin
  fapply category.mk,
  intros d₁ d₂, fapply adjointify, 
  { intro i, exact inj_imp inj d₁ d₂ (category.isotoid (ind_type_iso_iso f i)) },
  { intro i, apply hom_eq_to_iso_eq, 
    rwr ind_idtoiso_hom f inj (category.isotoid (ind_type_iso_iso f i)),
    change (idtoiso (idtoiso⁻¹ᶠ (ind_type_iso_iso f i))).hom = i.hom,
    rwr category.idtoiso_rinv (ind_type_iso_iso f i) },
  { intro p, hinduction p, rwr idtoiso_refl_eq d₁, 
    have H : ind_type_iso_iso f (id_is_iso d₁) = id_is_iso (f d₁), from 
      begin apply hom_eq_to_iso_eq, refl end,
    rwr H, rwr isotoid_id_refl, exact inj_idp d₁ }
end    

@[hott]
def emb_functor {C : Type u} [category.{v} C] {D : Type u'} (f : D -> C) : 
  (ind_cat_type f) ⥤ C :=
begin
  fapply functor.mk,
  { exact f },
  { intros x y h, exact h },
  { intro x, refl },
  { intros x y z g h, refl }
end  

/- The full subcategory on a subtype of the type of a category can be defined using
   the injctive embedding of the subtype into the type. -/
@[hott]
def subtype_emb {C : Type u} [category.{v} C] (P : C -> trunctype.{0} -1) :
  subtype (λ c : C, ↥(P c)) -> C := assume sc, sc.1

@[hott, instance]
def subtype_emb_is_inj {C : Type u} [category.{v} C] (P : C -> trunctype.{0} -1) :
  is_injective (subtype_emb P) :=
begin intros sc₁ sc₂, exact (subtype_eq_equiv sc₁ sc₂).to_is_equiv end    

@[hott, instance]
def full_subcat_on_subtype {C : Type u} [category.{v} C] (P : C -> trunctype.{0} -1) :
  category (subtype (λ c : C, ↥(P c))) :=
@fully_embedded_category _ _ _ (subtype_emb P) (subtype_emb_is_inj P)  

@[hott]
def embed {C : Type u} [category.{v} C] {P : C -> trunctype.{0} -1} 
  {D : Type u'} [precategory.{v'} D] (F : D ⥤ subtype (λ c : C, ↥(P c))) : D ⥤ C :=
F ⋙ (emb_functor (subtype_emb P))   

end categories

end hott