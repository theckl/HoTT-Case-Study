import categories.basic 

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.is_trunc hott.precategories hott.categories

/- In a category `C` we can define a subobject of an object `c` as a monomorphism `a ⟶ c`. Two 
   such subobjects are equal if and only if there is an isomorphism between the sources of the 
   monomorphisms factorizing the monomorphisms. Therefore in HoTT categories, it is not necessary 
   to define subobjects as isomorphism classes. -/
@[hott]  --[GEVE]
def is_mono {C : Type _} [is_cat C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) :=
  Π (d : C) (g₁ g₂ : d ⟶ c₁), g₁ ≫ f = g₂ ≫ f -> g₁ = g₂

@[hott]
def is_epi {C : Type _} [is_cat C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) :=
  Π (d : C) (g₁ g₂ : c₂ ⟶ d), f ≫ g₁ = f ≫ g₂ -> g₁ = g₂

@[hott, instance]
def is_mono_is_prop {C : Type _} [is_cat C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) : 
  is_prop (is_mono f) :=
begin apply is_prop_dprod, intro d, apply_instance end 

@[hott]
def is_mono_is_trans {C : Type _} [is_cat C] {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} 
  {g : c₂ ⟶ c₃} : is_mono f -> is_mono g -> is_mono (f ≫ g) :=
begin 
  intros Hf Hg d h₁ h₂, rwr <- is_precat.assoc, rwr <- is_precat.assoc, 
  intro H, exact Hf d h₁ h₂ (Hg d (h₁ ≫ f) (h₂ ≫ f) H) end  

@[hott]
def isos_are_mono {C : Type _} [is_cat C] {c₁ c₂ : C} (i : c₁ ≅ c₂) : is_mono i.hom :=  
  assume d g₁ g₂ eq_comp, 
  calc g₁ = g₁ ≫ 𝟙 c₁ : by rwr is_precat.comp_id
       ... = g₁ ≫ (i.hom ≫ i.ih.inv) : by rwr is_iso.l_inv
       ... = (g₁ ≫ i.hom) ≫ i.ih.inv : by rwr is_precat.assoc
       ... = (g₂ ≫ i.hom) ≫ i.ih.inv : by rwr eq_comp
       ... = g₂ : by rwr is_precat.assoc; rwr is_iso.l_inv; rwr is_precat.comp_id   

@[hott]
structure hom_of_monos {C : Type _} [is_cat C] {c d₁ d₂: C} {f : d₁ ⟶ c} 
  (Hf : is_mono f) {g : d₂ ⟶ c} (Hg : is_mono g) :=
(hom_obj : d₁ ⟶ d₂)
(fac : hom_obj ≫ g = f)

@[hott]
def hom_of_monos_is_mono {C : Type _} [is_cat C] {c d₁ d₂: C} {f : d₁ ⟶ c} 
  {Hf : is_mono f} {g : d₂ ⟶ c} {Hg : is_mono g} (hm : hom_of_monos Hf Hg) :
  is_mono hm.hom_obj :=
begin 
  intros d h₁ h₂ p, apply Hf, rwr <- hm.fac, 
  rwr <- is_precat.assoc, rwr <- is_precat.assoc, rwr p 
end

@[hott, instance]
def is_prop_hom_of_monos {C : Type _} [is_cat C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : is_prop (hom_of_monos Hf Hg) :=
begin 
  apply is_prop.mk, intros hm₁ hm₂, hinduction hm₁ with h₁ fac₁, hinduction hm₂ with h₂ fac₂, 
  fapply apd011 (hom_of_monos.mk Hf Hg), 
  { apply Hg, exact fac₁ ⬝ fac₂⁻¹ },
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end  

@[hott]
structure iso_of_monos {C : Type _} [is_cat C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) :=
(iso_obj : d₁ ≅ d₂)
(fac : iso_obj.hom ≫ g = f) 

@[hott]
def iso_of_monos_eq {C : Type _} [is_cat C] {c d₁ d₂: C} {f : d₁ ⟶ c} {Hf : is_mono f}
  {g : d₂ ⟶ c} {Hg : is_mono g} (im₁ im₂ : iso_of_monos Hf Hg) : 
  im₁.iso_obj = im₂.iso_obj -> im₁ = im₂ :=
begin 
  hinduction im₁ with iso_obj₁ fac₁, hinduction im₂ with iso_obj₂ fac₂, hsimp, 
  intro p, fapply apd011 (iso_of_monos.mk Hf Hg), assumption,
  apply pathover_of_tr_eq, exact is_set.elim _ _ 
end 

@[hott]
def homs_eqv_iso_of_monos {C : Type u} [is_cat.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : 
  (hom_of_monos Hf Hg) × (hom_of_monos Hg Hf) ≃ iso_of_monos Hf Hg :=
begin 
  fapply equiv.mk, 
  { intro homs, let sh₁ := homs.1, let sh₂ := homs.2, fapply iso_of_monos.mk, 
    { fapply iso.mk, 
      { exact sh₁.hom_obj },
      { fapply is_iso.mk,
        { exact sh₂.hom_obj },
        { apply Hg d₂ (sh₂.hom_obj ≫ sh₁.hom_obj) (𝟙 d₂), rwr is_precat.assoc, 
        rwr sh₁.fac, rwr sh₂.fac, hsimp },
        { apply Hf d₁ (sh₁.hom_obj ≫ sh₂.hom_obj) (𝟙 d₁), rwr is_precat.assoc, 
        rwr sh₂.fac, rwr sh₁.fac, hsimp } } },
    { hsimp, rwr sh₁.fac } },
  { fapply is_equiv.adjointify, 
    { intro i, fapply pair, 
      { fapply hom_of_monos.mk, exact i.iso_obj.hom, exact i.fac },
      { fapply hom_of_monos.mk, exact i.iso_obj.ih.inv, rwr iso_move_lr _ _ _ i.fac } },
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
def is_prop_iso_of_monos {C : Type u} [is_cat.{v} C] {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : is_prop (iso_of_monos Hf Hg) :=
begin apply is_trunc_equiv_closed -1 (homs_eqv_iso_of_monos Hf Hg), apply_instance end

@[hott]  --[GEVE]
def mono_is_faithful {C : Type _} [is_cat C] {D : Type _} [is_cat D] {F : C ⥤ D} [H : is_faithful_functor F] {c₁ c₂: C} :
  Π (f : c₁ ⟶ c₂), is_mono (F.map f) -> is_mono f :=
begin 
  intros f mono_F, intros d g₁ g₂ p, apply H, apply mono_F,
  rwr <- F.map_comp, rwr <- F.map_comp, exact ap (precategories.functor.map F) p 
end 

@[hott]  --[GEVE]
structure subobject {C : Type _} [is_cat C] (c : C) :=
  (obj : C)
  (hom : obj ⟶ c)
  (is_mono : is_mono hom)  

@[hott]
def subobject_eq {C : Type _} [is_cat C] {c : C} {s₁ s₂ : subobject c} :
  Π (p : s₁.obj = s₂.obj), s₁.hom =[p; λ a : C, a ⟶ c ] s₂.hom -> s₁ = s₂ :=
begin
  hinduction s₁ with a₁ h₁ mono₁, hinduction s₂ with a₂ h₂ mono₂,
  intros p q, fapply apd0111 subobject.mk, exact p, exact q, 
  apply pathover_of_tr_eq, exact is_prop.elim _ _
end

@[hott] 
def subobject_eq_idp {C : Type _} [is_cat C] {c : C} {s : subobject c} 
  {q : s.hom =[idp; λ a : C, a ⟶ c ] s.hom} :
  @subobject_eq C _ c s _ idp q = idp :=
begin
  have r : q = idpo, from begin apply is_prop.elim end,
  hinduction s with a h mono, rwr r, change apd0111 subobject.mk idp idpo _ = idp, 
  hsimp, refl
end

@[hott]
def subobject_eq_obj {C : Type _} [is_cat C] {c : C} {s₁ s₂ : subobject c} 
  {p : s₁.obj = s₂.obj} {q : s₁.hom =[p; λ a : C, a ⟶ c ] s₂.hom} :
  ap subobject.obj (subobject_eq p q) = p :=
begin
  hinduction s₁ with a₁ h₁ mono₁, hinduction s₂ with a₂ h₂ mono₂,
  change a₁ = a₂ at p, hinduction p, 
  change ap subobject.obj (apd0111 subobject.mk idp q _) = idp, 
  let HP : Π (a : C) (h : a ⟶ c) (m : is_mono h), 
              subobject.obj (subobject.mk a h m) = a := assume a h m, rfl,
  rwr ap_apd0111 subobject.mk idp q _ subobject.obj HP
end

/- A homomorphism between subobjects compatible with the injections is itself an injection. Hence,
   homomorphisms between subobjects in both ways imply an isomorphism of subobjects and therefore
   equality. -/
@[hott]
def subobject_hom {C : Type _} [is_cat C] {c : C} (s₁ s₂ : subobject c) :=
  hom_of_monos s₁.is_mono s₂.is_mono

@[hott, instance]
def subobject_hom_is_prop {C : Type _} [is_cat C] {c : C} (s₁ s₂ : subobject c) :
  is_prop (subobject_hom s₁ s₂) :=
begin change is_prop (hom_of_monos s₁.is_mono s₂.is_mono), apply_instance end    

@[hott]
def equal_subobj_to_iso_mono {C : Type _} [is_cat C] {c : C} (s₁ s₂ : subobject c) :
  s₁ = s₂ -> iso_of_monos s₁.is_mono s₂.is_mono :=
begin 
  intro p, fapply iso_of_monos.mk, 
  exact (idtoiso (ap subobject.obj p)), 
  hinduction p, hsimp 
end  

@[hott] 
def idp_subobj_to_iso_mono {C : Type _} [is_cat C] {c : C} (s : subobject c) :
  equal_subobj_to_iso_mono s s idp = iso_of_monos.mk s.is_mono s.is_mono (id_iso s.obj) 
                                                     (is_precat.id_comp s.hom) :=
begin apply iso_of_monos_eq, change idtoiso idp = id_iso s.obj, rwr idtoiso_refl_eq end                                                     

@[hott, reducible]
def iso_mono_to_equal_subobj {C : Type _} [is_cat C] {c : C} (s₁ s₂ : subobject c) :
  iso_of_monos s₁.is_mono s₂.is_mono -> s₁ = s₂ :=
begin
  intro im, fapply subobject_eq,
  { exact idtoiso⁻¹ᶠ im.iso_obj },
  { apply pathover_of_tr_eq, rwr iso_hom_tr_comp, 
    apply eq.inverse, apply iso_move_lr, rwr im.fac }
end

@[hott]
def iso_mono_to_equal_subobj_iso {C : Type _} [is_cat C] {c : C} {s₁ s₂ : subobject c} 
  (im : iso_of_monos s₁.is_mono s₂.is_mono) : 
  ap subobject.obj (iso_mono_to_equal_subobj s₁ s₂ im) = category.isotoid im.iso_obj :=
begin
  hinduction s₁ with obj₁ hom₁ is_mono₁, hinduction s₂ with obj₂ hom₂ is_mono₂,
  change ap subobject.obj (subobject_eq _ _) = _, rwr subobject_eq_obj   
end    

@[hott]
def equal_subobj_eqv_iso_mono {C : Type _} [is_cat C] {c : C} (s₁ s₂ : subobject c) :
  s₁ = s₂ ≃ iso_of_monos s₁.is_mono s₂.is_mono :=
begin
  fapply equiv.mk,
  { exact equal_subobj_to_iso_mono s₁ s₂ },
  { fapply is_equiv.adjointify,
    { exact iso_mono_to_equal_subobj s₁ s₂ },
    { hinduction s₁ with obj₁ hom₁ is_mono₁, hinduction s₂ with obj₂ hom₂ is_mono₂,
      intro im, hinduction im with iso_obj fac, apply iso_of_monos_eq _ _, hsimp,
      change idtoiso (ap subobject.obj _) = _, rwr iso_mono_to_equal_subobj_iso,
      rwr category.idtoiso_rinv' },
    { intro p, hinduction p, rwr idp_subobj_to_iso_mono,
      change subobject_eq (category.isotoid (id_iso s₁.obj)) _ = _,
      rwr fn2_ev_fn2_tr' _ _ subobject_eq, rwr subobject_eq_idp, 
      exact isotoid_id_refl s₁.obj } }
end


/- The subobjects of an object in a HoTT-category form a set, so a HoTT-category is 
   well-powered. -/
@[hott, instance]
def subobject_is_set {C : Type _} [is_cat C] (c : C) : is_set (subobject c) :=
begin 
  apply is_trunc_succ_intro, intros s₁ s₂, 
  apply is_trunc_equiv_closed_rev -1 (equal_subobj_eqv_iso_mono s₁ s₂), 
  apply is_trunc_equiv_closed -1 (homs_eqv_iso_of_monos s₁.is_mono s₂.is_mono), 
  apply_instance 
end

@[hott]
def Subobject {C : Type _} [is_cat C] (c : C) : Set :=
  Set.mk (subobject c) (subobject_is_set c)

/- The subobjects of an object, together with their monomorphism-preserving homomorphisms
   defined in [categories.basic], form a category. -/  
@[hott, instance]
def subobject_has_hom {C : Type _} [is_cat C] {c : C} : has_hom (subobject c) :=
  has_hom.mk (λ a b : subobject c, Set.mk (subobject_hom a b) (is_trunc_succ _ -1))

@[hott]
def id_subobject {C : Type _} [is_cat C] {c : C} (a : subobject c) : subobject_hom a a :=
  begin fapply hom_of_monos.mk a.is_mono a.is_mono, exact 𝟙 a.obj, hsimp end  

@[hott] 
def comp_subobject {C : Type _} [is_cat C] {c : C} (a₁ a₂ a₃ : subobject c) :
  subobject_hom a₁ a₂ -> subobject_hom a₂ a₃ -> subobject_hom a₁ a₃ :=
begin 
  intros f g, fapply hom_of_monos.mk a₁.is_mono a₃.is_mono, exact f.hom_obj ≫ g.hom_obj, 
  rwr is_precat.assoc, rwr g.fac, rwr f.fac 
end  

@[hott, instance]
def subobject_cat_struct {C : Type _} [is_cat C] {c : C} : 
  category_struct (subobject c) :=
category_struct.mk id_subobject comp_subobject

@[hott, instance]
def subobject_is_precat {C : Type _} [is_cat C] {c : C} : 
  is_precat (subobject c) :=
have ic : Π (a b : subobject c) (f : a ⟶ b), 𝟙 a ≫ f = f, from 
  assume a b f, by exact is_prop.elim _ _,
have ci : Π (a b : subobject c) (f : a ⟶ b), f ≫ 𝟙 b = f, from 
  assume a b f, by exact is_prop.elim _ _,
have as : Π (a₁ a₂ a₃ a₄ : subobject c) (f : a₁ ⟶ a₂) (g : a₂ ⟶ a₃) (h : a₃ ⟶ a₄),
             (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
  assume a₁ a₂ a₃ a₄ f g h, by exact is_prop.elim _ _,
is_precat.mk ic ci as  

@[hott]
def iso_of_monos_to_iso {C : Type _} [is_cat C] {c : C} (a b : subobject c) :
  (iso_of_monos a.is_mono b.is_mono) -> (a ≅ b) :=
begin 
  intro im, fapply iso.mk, 
  { fapply hom_of_monos.mk, exact im.iso_obj.hom, exact im.fac }, 
  { fapply is_iso.mk,
    fapply hom_of_monos.mk, exact im.iso_obj.ih.inv, apply eq.inverse, apply iso_move_lr, 
    exact im.fac, exact is_prop.elim _ _, exact is_prop.elim _ _ } 
end

@[hott]
def iso_to_iso_of_monos {C : Type _} [is_cat C] {c : C} (a b : subobject c) :
  (a ≅ b) -> (iso_of_monos a.is_mono b.is_mono) :=
begin 
  intro i, fapply iso_of_monos.mk, 
  { fapply iso.mk, exact i.hom.hom_obj, fapply is_iso.mk, 
    exact i.ih.inv.hom_obj, 
    exact ap hom_of_monos.hom_obj i.ih.r_inv, 
    exact ap hom_of_monos.hom_obj i.ih.l_inv },
  { exact i.hom.fac }
end    

@[hott]
def iso_of_monos_eqv_iso {C : Type u} [is_cat.{v} C] {c : C} (a b : subobject c) :
  (iso_of_monos a.is_mono b.is_mono) ≃ (a ≅ b) :=
begin 
  fapply equiv.mk,
  { exact iso_of_monos_to_iso a b },
  { fapply is_equiv.adjointify, 
    { exact iso_to_iso_of_monos a b },
    { intro i, apply hom_eq_to_iso_eq, exact is_prop.elim _ _ },
    { intro i, exact @is_prop.elim _ 
              (is_prop_iso_of_monos a.is_mono b.is_mono) _ _ } }
end  

@[hott]
def subobj_idtoiso {C : Type u} [is_cat.{v} C] {c : C} (a b : subobject c) : 
  @idtoiso _ _ a b = (iso_of_monos_eqv_iso a b).to_fun ∘ 
                     (equal_subobj_eqv_iso_mono a b).to_fun :=
begin apply eq_of_homotopy, intro p, apply hom_eq_to_iso_eq, exact is_prop.elim _ _ end                       

@[hott, instance]
def subobject_is_cat {C : Type u} [is_cat.{v} C] {c : C} : 
  is_cat (subobject c) :=
begin apply is_cat.mk, intros a b, rwr subobj_idtoiso a b, apply_instance end    

@[hott]
def subobject_Category {C : Type _} [is_cat C] (c : C) : Category :=
  Category.mk (subobject c) subobject_is_cat

/- Since homomorphisms between subobjects are unique and anti-symmetric (see below), 
   they can be seen as an order on the set of subobjects. To emphasize this point of 
   view, we introduce a `≤`-notation for these homomorphisms. 
   
   A `has_le`-class is introduced in [algebra.order], but there seems to be universe
   problems when used with subobjects in categories. -/
@[hott]
class has_order (A : Type _) := (le : A → A → Type _)

hott_theory_cmd "local infix ` ≼ `:60  := hott.has_order.le"

@[hott, instance]
def subobject_has_order {C : Type _} [is_cat C] (c : C) : 
  has_order (subobject c) :=
  has_order.mk (λ a b, a ⟶ b)  

@[hott]
def subobj_antisymm {C : Type u} [is_cat.{v} C] {c : C} (a b : subobject c) : 
  (a ≼ b) -> (b ≼ a) -> (a = b) :=
begin 
  intros i j , 
  have iso_ab : a ≅ b, from 
    begin 
      fapply iso.mk, exact i, fapply is_iso.mk, exact j, 
      exact @is_prop.elim _ (subobject_hom_is_prop b b) _ _, 
      exact @is_prop.elim _ (subobject_hom_is_prop a a) _ _ 
    end,  
  exact @category.isotoid (subobject c) subobject_is_cat _ _ iso_ab 
end  

@[hott]
def subobj_trans {C : Type _} [is_cat C] {d : C} {a b c : subobject d} : 
  (a ≼ b) -> (b ≼ c) -> (a ≼ c) :=
λ i j, i ≫ j 

@[hott]
def subobj_subobj_trans {C : Type _} [is_cat C] {c : C} (a : subobject c) 
  (b : subobject a.obj) : subobject c :=
subobject.mk b.obj (b.hom ≫ a.hom) (is_mono_is_trans b.is_mono a.is_mono) 

@[hott]
def subobj_trans_hom_hom {C : Type _} [is_cat C] {c : C} (a : subobject c) 
  (b : subobject a.obj) : (subobj_subobj_trans a b).hom = b.hom ≫ a.hom := rfl

@[hott]
def subobj_subobj_trans_hom {C : Type _} [is_cat C] {c : C} (a : subobject c) 
  (b : subobject a.obj) : subobj_subobj_trans a b ≼ a :=
begin fapply hom_of_monos.mk, exact b.hom, refl end

@[hott]
def subobj_subobj_trans_pres_hom {C : Type _} [is_cat C] {d : C} (a : subobject d) 
  (b c : subobject a.obj) : b ≼ c -> subobj_subobj_trans a b ≼ subobj_subobj_trans a c :=
begin
  intro bc, fapply hom_of_monos.mk, 
  { exact bc.hom_obj },
  { change _ ≫ c.hom ≫ a.hom = b.hom ≫ a.hom, rwr <- is_precat.assoc, rwr bc.fac }
end

@[hott]
def subobj_rest {C : Type _} [is_cat C] {c : C} {a b : subobject c} (f : b ≼ a) :
  subobject a.obj := 
subobject.mk b.obj f.hom_obj (hom_of_monos_is_mono f)

@[hott]
def subobj_hom_rest {C : Type _} [is_cat C] {c : C} {a b b': subobject c} (f : b ≼ a) 
  (f' : b' ≼ a) (g : b ≼ b') : (subobj_rest f) ⟶ (subobj_rest f') :=
begin 
  fapply hom_of_monos.mk, exact g.hom_obj, change (g ≫ f').hom_obj = f.hom_obj,
  apply ap hom_of_monos.hom_obj, exact is_prop.elim _ _
end

@[hott]
def subobj_hom_rest_hom {C : Type _} [is_cat C] {c : C} {a b b': subobject c} (f : b ≼ a) 
  (f' : b' ≼ a) (g : subobj_rest f ≼ subobj_rest f') : b ≼ b' :=
begin 
  fapply hom_of_monos.mk, exact g.hom_obj, 
  rwr <- f'.fac, rwr <- f.fac, rwr <- is_precat.assoc,
  apply ap (λ h : b.obj ⟶ a.obj, h ≫ a.hom), 
  change _ ≫ (subobj_rest f').hom = _, rwr g.fac
end  

@[hott]
def subobj_rest_trans {C : Type _} [is_cat C] {c : C} (a : subobject c) (b : subobject a.obj) :
  subobj_rest (subobj_subobj_trans_hom a b) = b :=
begin 
  fapply subobj_antisymm,
  { fapply hom_of_monos.mk, 
    { exact 𝟙 b.obj },
    { rwr is_precat.id_comp b.hom } },
  { fapply hom_of_monos.mk,
    { exact 𝟙 b.obj },
    { rwr is_precat.id_comp } } 
end

@[hott]
def subobj_trans_hom_to_hom {C : Type _} [is_cat C] {c : C} (a : subobject c) (b b' : subobject a.obj) :
  (subobj_subobj_trans a b) ≼ (subobj_subobj_trans a b') -> b ≼ b' :=
begin
  intro trans_inc, fapply hom_of_monos.mk,
  { exact trans_inc.hom_obj },
  { apply a.is_mono, rwr is_precat.assoc, exact trans_inc.fac } 
end

/- The category of subobjects always has a top element. -/
@[hott]
def top_subobject {C : Type _} [is_cat C] (c : C) : subobject c := 
  subobject.mk c (𝟙 c) (isos_are_mono (id_iso c))

@[hott]
def top_subobj_prop {C : Type _} [is_cat C] {c : C} : 
  Π (a : subobject c), a ≼ top_subobject c := 
begin intro a, fapply hom_of_monos.mk, exact a.hom, hsimp end 

@[hott]
def top_subobj_unique {C : Type _} [is_cat C] {c : C} (d : subobject c) :
  (Π (a : subobject c), a ≼ d) -> d = top_subobject c :=
begin intro max, fapply subobj_antisymm, exact top_subobj_prop d, exact max _ end

@[hott]
def top_subobj_is_top {C : Type _} [is_cat C] {c : C} (b : subobject c) : b ≼ top_subobject c :=
begin
  fapply hom_of_monos.mk b.is_mono (top_subobject c).is_mono b.hom, 
  change _ ≫ 𝟙 c = _, rwr is_precat.comp_id
end 

@[hott]
def trans_top_subobj_subobj {C : Type _} [is_cat C] {c : C} (b : subobject c) :
  subobj_subobj_trans b (top_subobject b.obj) = b :=
begin
  fapply subobj_antisymm, 
  { fapply hom_of_monos.mk, exact 𝟙 b.obj, change _ = 𝟙 b.obj ≫ _, exact idp },
  { fapply hom_of_monos.mk, exact 𝟙 b.obj, change _ ≫ (𝟙 b.obj ≫ _) = _, 
    rwr is_precat.id_comp, rwr is_precat.id_comp }
end

/- We can define images of homomorphisms as subobjects of their codomain satisfying a 
   minimality property. Note that the factoring homomorphism is unique as the inclusion 
   homomorphism is a monomorphism. -/
@[hott]
structure is_image {C : Type _} [is_cat C] {c d : C} (f : c ⟶ d) (d' : subobject d) :=
  (fac : Σ f' : c ⟶ d'.obj, f' ≫ d'.hom = f)
  (univ : Π (a : subobject d), (Σ f' : c ⟶ a.obj, f' ≫ a.hom = f) -> (d' ≼ a))

@[hott] 
def subobject_fac_is_unique {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) 
  (a : subobject d) : Π fac₁ fac₂ : (Σ (f' : c ⟶ a.obj), f' ≫ a.hom = f), fac₁ = fac₂ :=
begin 
  intros fac₁ fac₂, fapply sigma.sigma_eq, 
  { fapply a.is_mono, exact fac₁.2 ⬝ fac₂.2⁻¹ }, 
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott, instance] 
def subobject_fac_is_prop {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) 
  (a : subobject d) : is_prop (Σ f' : c ⟶ a.obj, f' ≫ a.hom = f) :=
is_prop.mk (subobject_fac_is_unique f a)  


@[hott]
def image_is_unique {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) {d₁ d₂ : subobject d} :
  is_image f d₁ -> is_image f d₂ -> d₁ = d₂ :=
begin
  intros im₁ im₂, 
  hinduction im₁ with fac₁ univ₁, hinduction im₂ with fac₂ univ₂, 
  fapply subobj_antisymm, exact univ₁ d₂ fac₂, exact univ₂ d₁ fac₁
end  

@[hott, instance]
def is_image_is_prop {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) (d' : subobject d) : 
  is_prop (is_image f d') :=
begin 
  fapply is_prop.mk, intros is_im₁ is_im₂,
  hinduction is_im₁ with fac₁ univ₁, hinduction is_im₂ with fac₂ univ₂, 
  fapply ap011 is_image.mk, apply subobject_fac_is_unique, exact is_prop.elim _ _ 
end  

@[hott]
class has_image {C : Type _} [is_cat C] {c d : C} (f : c ⟶ d) :=
  (im : subobject d)
  (is_im : is_image f im)

@[hott, instance]
def has_im_is_prop {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) : is_prop (has_image f) :=
begin 
  apply is_prop.mk, intros hi₁ hi₂, hinduction hi₁ with im₁ is_im₁, hinduction hi₂ with im₂ is_im₂,
  fapply apd011 has_image.mk, exact image_is_unique f is_im₁ is_im₂, apply pathover_of_tr_eq,
  exact is_prop.elim _ _ 
end

@[hott, reducible]
def hom.image {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) [has_image f] : 
  subobject d :=  
has_image.im f

@[hott, reducible]
def hom_to_image {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) [has_image f] :
  c ⟶ (hom.image f).obj := 
(has_image.is_im f).fac.1  

@[hott]
def hom_to_image_eq {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) [has_image f] :
  hom_to_image f ≫ (hom.image f).hom = f := 
(has_image.is_im f).fac.2 

@[hott]
def hom_image_univ {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) [has_image f] :
  Π (a : subobject d) (f' : c ⟶ a.obj), f' ≫ a.hom = f -> (hom.image f ≼ a) :=
assume a f' p, (has_image.is_im f).univ a ⟨f', p⟩ 

@[hott]
def subobj_has_im {C : Type u} [is_cat.{v} C] {c : C} (b : subobject c) :
  has_image b.hom :=
have im_b : is_image b.hom b, from 
  is_image.mk (sigma.mk (𝟙 b.obj) (is_precat.id_comp b.hom)) 
               (λ a m, hom_of_monos.mk _ _ m.1 m.2),  
has_image.mk b im_b

@[hott]
def subobj_is_im {C : Type u} [is_cat.{v} C] {c : C} (b : subobject c) [has_image b.hom]:
  hom.image b.hom = b := 
begin 
  fapply subobj_antisymm, 
  { fapply hom_image_univ, exact 𝟙 b.obj, apply is_precat.id_comp }, 
  { fapply hom_of_monos.mk, exact hom_to_image b.hom, exact hom_to_image_eq b.hom } 
end  

@[hott]
def im_incl {C : Type u} [is_cat.{v} C] {a b c : C} (f : a ⟶ b) (g : b ⟶ c) 
  [has_image (f ≫ g)] [has_image g] : hom.image (f ≫ g) ≼ hom.image g :=
begin 
  fapply is_image.univ (has_image.is_im (f ≫ g)), fapply sigma.mk, 
  { exact f ≫ hom_to_image g }, 
  { rwr is_precat.assoc, rwr hom_to_image_eq g }
end  

@[hott]
def im_incl_eq {C : Type u} [is_cat.{v} C] 
  {c d : C} (a : subobject c) (f : d ⟶ a.obj) [has_image f] [has_image (f ≫ a.hom)] : 
  (hom.image (f ≫ a.hom)) = (subobj_subobj_trans a (hom.image f)) :=
begin 
  have p : hom_to_image f ≫ (subobj_subobj_trans a (hom.image f)).hom = f ≫ a.hom, from
    begin change _ ≫ _ ≫ _ = _, rwr <- is_precat.assoc, rwr hom_to_image_eq end,
  let g := hom_image_univ (f ≫ a.hom) (subobj_subobj_trans a (hom.image f)) 
                                                                   (hom_to_image f) p,
  fapply subobj_antisymm, 
  { exact g }, 
  { fapply @subobj_hom_rest_hom _ _ _ a, 
    { exact subobj_subobj_trans_hom _ _ },
    { exact g ≫ subobj_subobj_trans_hom _ _ },
    { rwr subobj_rest_trans, fapply hom_image_univ, 
      { exact hom_to_image (f ≫ a.hom) },
      { fapply a.is_mono, apply λ p, p ⬝ hom_to_image_eq (f ≫ a.hom), 
        rwr is_precat.assoc, 
        change _ ≫ (g ≫ subobj_subobj_trans_hom a (hom.image f)).hom_obj ≫ _ = _,
        rwr (g ≫ subobj_subobj_trans_hom a (hom.image f)).fac } } }
end

@[hott]
def im_iso_comp {C : Type u} [is_cat.{v} C] {a b c : C} (i : a ≅ b) (g : b ⟶ c) 
  [has_image (i.hom ≫ g)] [has_image g] : hom.image (i.hom ≫ g) = hom.image g :=
begin
  apply subobj_antisymm,
  { fapply hom_image_univ,
    { exact i.hom ≫ hom_to_image g },
    { rwr is_precat.assoc, rwr hom_to_image_eq } },
  { fapply hom_image_univ, 
    { exact i.ih.inv ≫ hom_to_image (i.hom ≫ g) },
    { rwr is_precat.assoc, rwr hom_to_image_eq, rwr <- is_precat.assoc, 
      rwr i.ih.r_inv, rwr is_precat.id_comp } }
end

@[hott]
class has_images (C : Type u) [is_cat.{v} C] :=
  (has_im : Π {c d : C} (f : c ⟶ d), has_image f)

@[hott, instance]
def has_ims_is_prop {C : Type u} [is_cat.{v} C] : is_prop (has_images C) :=
begin 
  apply is_prop.mk, intros hi₁ hi₂, hinduction hi₁, hinduction hi₂,
  apply ap has_images.mk, exact is_prop.elim _ _ 
end

@[hott, instance]
def has_image_of_has_images {C : Type u} [is_cat.{v} C] [has_images C] {c d : C} 
  (f : c ⟶ d) : has_image f :=
has_images.has_im f

@[hott]
def mono_is_image {C : Type u} [is_cat.{v} C] {c d : C} 
  (f : c ⟶ d) [has_image f] (mon_f : is_mono f) : hom.image f ≅ subobject.mk c f mon_f :=
begin
  fapply iso.mk,
  { apply is_image.univ (has_image.is_im f), apply dpair (𝟙 c), apply is_precat.id_comp },
  { fapply is_iso.mk,
    { fapply hom_of_monos.mk, apply hom_to_image, apply hom_to_image_eq },
    { apply @is_prop.elim _ (is_prop_hom_of_monos _ _) _ _ },
    { apply @is_prop.elim _ (is_prop_hom_of_monos _ _) _ _ } }
end  

@[hott]
def is_surj {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) [has_image f] := 
  hom.image f ≅ top_subobject d 

@[hott]
def mor_to_im_is_surj {C : Type u} [is_cat.{v} C] {c d : C} (f : c ⟶ d) [has_images C] :
  is_surj (hom_to_image f) :=
begin
  fapply iso.mk,
  { apply top_subobj_is_top },
  { fapply is_iso.mk,
    { apply subobj_trans_hom_to_hom, rwr trans_top_subobj_subobj, fapply hom_image_univ,
      { apply hom_to_image },
      { change _ ≫ _ ≫ _ = _, rwr <- is_precat.assoc, rwr hom_to_image_eq, rwr hom_to_image_eq } },
    { apply @is_prop.elim _ (is_prop_hom_of_monos _ _) _ _ },
    { apply @is_prop.elim _ (is_prop_hom_of_monos _ _) _ _ } }  
end

@[hott]
def surj_mono_surj_iso  {C : Type u} [is_cat.{v} C] [has_images C] {c d e : C} 
  (f : c ⟶ d) (i : d ⟶ e) : is_surj f -> is_mono i -> is_surj (f ≫ i) -> is_iso i :=
begin
  intros surj_f mono_i surj_fi, fapply is_iso.mk,
  { apply category_struct.comp (is_iso.inv surj_fi.ih).hom_obj, 
    apply category_struct.comp (im_incl f i).hom_obj, 
    exact (mono_is_image i mono_i).hom.hom_obj },
  { rwr is_precat.assoc, rwr is_precat.assoc _ _ i, rwr (mono_is_image i mono_i).hom.fac, 
    rwr (im_incl f i).fac, rwr surj_fi.ih.inv.fac },
  { apply mono_i, rwr is_precat.assoc i, rwr is_precat.assoc _ _ i, rwr is_precat.assoc _ _ i,
    rwr (mono_is_image i mono_i).hom.fac, rwr (im_incl f i).fac, rwr surj_fi.ih.inv.fac, 
    change i ≫ 𝟙 e = _, rwr is_precat.comp_id, rwr is_precat.id_comp }
end

@[hott]
def hom_obj_iso_subobj_eq {C : Type u} [is_cat.{v} C] {c : C} {b b' : subobject c} (i : b ≼ b') :
  is_iso i.hom_obj -> b = b' :=
begin
  intro ih, fapply subobj_antisymm, exact i, fapply hom_of_monos.mk, exact ih.inv,
  rwr <- i.fac, rwr <- is_precat.assoc, rwr ih.r_inv, exact is_precat.id_comp _
end

end hott