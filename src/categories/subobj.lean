import sets.algebra init2 types2 sets.axioms categories.basic

universes v v' v'' v''' u u' u'' u''' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc 
     hott.is_equiv hott.trunc hott.precategories hott.categories

/- In a category `C` we can define a subobject of an object `c` as a monomorphism `a ⟶ c`. Two 
   such subobjects are equal if and only if there is an isomorphism between the sources of the 
   monomorphisms factorizing the monomorphisms. Therefore in HoTT categories, it is not necessary 
   to define subobjects as isomorphism classes. -/
@[hott]
def is_mono {C : Category} {c₁ c₂ : C} (f : c₁ ⟶ c₂) :=
  Π (d : C) (g₁ g₂ : d ⟶ c₁), g₁ ≫ f = g₂ ≫ f -> g₁ = g₂

@[hott, instance]
def is_mono_is_prop {C : Category} {c₁ c₂ : C} (f : c₁ ⟶ c₂) : 
  is_prop (is_mono f) :=
begin apply is_prop_dprod, intro d, apply_instance end 

@[hott]
def is_mono_is_trans {C : Category} {c₁ c₂ c₃ : C} {f : c₁ ⟶ c₂} 
  {g : c₂ ⟶ c₃} : is_mono f -> is_mono g -> is_mono (f ≫ g) :=
begin 
  intros Hf Hg d h₁ h₂, rwr <- is_precat.assoc, rwr <- is_precat.assoc, 
  intro H, exact Hf d h₁ h₂ (Hg d (h₁ ≫ f) (h₂ ≫ f) H) end  

@[hott]
def isos_are_mono {C : Category} {c₁ c₂ : C} (i : c₁ ≅ c₂) : is_mono i.hom :=  
  assume d g₁ g₂ eq_comp, 
  calc g₁ = g₁ ≫ 𝟙 c₁ : by rwr is_precat.comp_id
       ... = g₁ ≫ (i.hom ≫ i.inv) : by rwr iso.l_inv
       ... = (g₁ ≫ i.hom) ≫ i.inv : by rwr is_precat.assoc
       ... = (g₂ ≫ i.hom) ≫ i.inv : by rwr eq_comp
       ... = g₂ : by rwr is_precat.assoc; rwr iso.l_inv; rwr is_precat.comp_id   

@[hott]
structure hom_of_monos {C : Category} {c d₁ d₂: C} {f : d₁ ⟶ c} 
  (Hf : is_mono f) {g : d₂ ⟶ c} (Hg : is_mono g) :=
(hom_obj : d₁ ⟶ d₂)
(fac : hom_obj ≫ g = f)

@[hott, instance]
def is_prop_hom_of_monos {C : Category} {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : is_prop (hom_of_monos Hf Hg) :=
begin 
  apply is_prop.mk, intros hm₁ hm₂, hinduction hm₁ with h₁ fac₁, hinduction hm₂ with h₂ fac₂, 
  fapply apd011 (hom_of_monos.mk Hf Hg), 
  { apply Hg, exact fac₁ ⬝ fac₂⁻¹ },
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end  

@[hott]
structure iso_of_monos {C : Category} {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) :=
(iso_obj : d₁ ≅ d₂)
(fac : iso_obj.hom ≫ g = f) 

@[hott]
def iso_of_monos_eq {C : Category} {c d₁ d₂: C} {f : d₁ ⟶ c} {Hf : is_mono f}
  {g : d₂ ⟶ c} {Hg : is_mono g} (im₁ im₂ : iso_of_monos Hf Hg) : 
  im₁.iso_obj = im₂.iso_obj -> im₁ = im₂ :=
begin 
  hinduction im₁ with iso_obj₁ fac₁, hinduction im₂ with iso_obj₂ fac₂, hsimp, 
  intro p, fapply apd011 (iso_of_monos.mk Hf Hg), assumption,
  apply pathover_of_tr_eq, exact is_set.elim _ _ 
end 

@[hott]
def homs_eqv_iso_of_monos {C : Category} {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : 
  (hom_of_monos Hf Hg) × (hom_of_monos Hg Hf) ≃ iso_of_monos Hf Hg :=
begin 
  fapply equiv.mk, 
  { intro homs, let sh₁ := homs.1, let sh₂ := homs.2, fapply iso_of_monos.mk, 
    { fapply iso.mk, 
      { exact sh₁.hom_obj },
      { exact sh₂.hom_obj },
      { apply Hg d₂ (sh₂.hom_obj ≫ sh₁.hom_obj) (𝟙 d₂), rwr is_precat.assoc, 
        rwr sh₁.fac, rwr sh₂.fac, hsimp },
      { apply Hf d₁ (sh₁.hom_obj ≫ sh₂.hom_obj) (𝟙 d₁), rwr is_precat.assoc, 
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
def is_prop_iso_of_monos {C : Category} {c d₁ d₂: C} {f : d₁ ⟶ c} (Hf : is_mono f)
  {g : d₂ ⟶ c} (Hg : is_mono g) : is_prop (iso_of_monos Hf Hg) :=
begin apply is_trunc_equiv_closed -1 (homs_eqv_iso_of_monos Hf Hg), apply_instance end

@[hott]
structure subobject {C : Category} (c : C) :=
  (obj : C)
  (hom : obj ⟶ c)
  (is_mono : is_mono hom)  

@[hott]
def subobject_eta {C : Category} {c : C} (so : subobject c) :
  so = subobject.mk so.obj so.hom so.is_mono :=
begin hinduction so, refl end   

@[hott]
def subobject_eta_eq {C : Category} {c : C} (obj : C) (hom : obj ⟶ c) 
  (is_mono : is_mono hom) : subobject_eta (subobject.mk obj hom is_mono) = idp :=
rfl  

@[hott] 
def subobject_eq_idp {C : Category} {c : C} {s : subobject c} 
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

/- A homomorphism between subobjects compatible with the injections is itself an injection. Hence,
   homomorphisms between subobjects in both ways imply an isomorphism of subobjects and therefore
   equality. -/
@[hott]
def subobject_hom {C : Category} {c : C} (s₁ s₂ : subobject c) :=
  hom_of_monos s₁.is_mono s₂.is_mono

@[hott, instance]
def subobject_hom_is_prop {C : Category} {c : C} (s₁ s₂ : subobject c) :
  is_prop (subobject_hom s₁ s₂) :=
begin change is_prop (hom_of_monos s₁.is_mono s₂.is_mono), apply_instance end    

@[hott]
def equal_subobj_to_iso_mono {C : Category} {c : C} (s₁ s₂ : subobject c) :
  s₁ = s₂ -> iso_of_monos s₁.is_mono s₂.is_mono :=
begin 
  intro p, fapply iso_of_monos.mk, 
  exact (idtoiso (ap subobject.obj p)), 
  hinduction p, hsimp 
end  

@[hott] 
def idp_subobj_to_iso_mono {C : Category} {c : C} (s : subobject c) :
  equal_subobj_to_iso_mono s s idp = iso_of_monos.mk s.is_mono s.is_mono (id_iso s.obj) 
                                                     (is_precat.id_comp s.hom) :=
begin apply iso_of_monos_eq, change idtoiso idp = id_iso s.obj, rwr idtoiso_refl_eq end                                                     

@[hott]
def iso_mono_to_equal_subobj {C : Category} {c : C} (s₁ s₂ : subobject c) :
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
         ... = ((im.iso_obj)⁻¹ʰ ≫ im.iso_obj.hom) ≫ s₂.hom : 
               by rwr is_precat.assoc
         ... = 𝟙 s₂.obj ≫ s₂.hom : by rwr iso.r_inv 
         ... = s₂.hom : by rwr is_precat.id_comp },
  { apply pathover_of_tr_eq, apply eq_of_homotopy3, intros d g₁ g₂, 
    apply eq_of_homotopy, intro comp_eq, exact is_prop.elim _ _ } 
end 
⬝ (subobject_eta s₂)⁻¹  

@[hott]
def iso_mono_to_equal_subobj_iso {C : Category} {c : C} {s₁ s₂ : subobject c} 
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
def equal_subobj_eqv_iso_mono {C : Category} {c : C} (s₁ s₂ : subobject c) :
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
      change (subobject_eta _) ⬝ (apd0111 subobject.mk (category.isotoid (id_iso s₁.obj)) _ _) ⬝ 
                                                                                              _ = _, 
      apply con_eq_of_eq_con_inv, apply con_eq_of_eq_inv_con, rwr idp_con, 
      rwr con.right_inv, apply subobject_eq_idp, rwr isotoid_id_refl } }
end    

/- The subobjects of an object in a HoTT-category form a set, so a HoTT-category is well-powered. -/
@[hott, instance]
def subobject_is_set {C : Category} {c : C} : is_set (subobject c) :=
begin 
  apply is_trunc_succ_intro, intros s₁ s₂, 
  apply is_trunc_equiv_closed_rev -1 (equal_subobj_eqv_iso_mono s₁ s₂), 
  apply is_trunc_equiv_closed -1 (homs_eqv_iso_of_monos s₁.is_mono s₂.is_mono), 
  apply_instance 
end

/- The subobjects of an object, together with their monomorphism-preserving homomorphisms
   defined in [categories.basic], form a category. -/  
@[hott, instance]
def subobject_has_hom {C : Category} {c : C} : has_hom (subobject c) :=
  has_hom.mk (λ a b : subobject c, Set.mk (subobject_hom a b) (is_trunc_succ _ -1))

@[hott]
def id_subobject {C : Category} {c : C} (a : subobject c) : subobject_hom a a :=
  begin fapply hom_of_monos.mk a.is_mono a.is_mono, exact 𝟙 a.obj, hsimp end  

@[hott] 
def comp_subobject {C : Category} {c : C} (a₁ a₂ a₃ : subobject c) :
  subobject_hom a₁ a₂ -> subobject_hom a₂ a₃ -> subobject_hom a₁ a₃ :=
begin 
  intros f g, fapply hom_of_monos.mk a₁.is_mono a₃.is_mono, exact f.hom_obj ≫ g.hom_obj, 
  rwr is_precat.assoc, rwr g.fac, rwr f.fac 
end  

@[hott, instance]
def subobject_cat_struct {C : Category} {c : C} : 
  category_struct (subobject c) :=
category_struct.mk id_subobject comp_subobject

@[hott, instance]
def subobject_is_precat {C : Category} {c : C} : 
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
def iso_of_monos_to_iso {C : Category} {c : C} (a b : subobject c) :
  (iso_of_monos a.is_mono b.is_mono) -> (a ≅ b) :=
begin 
  intro im, fapply iso.mk, 
  { fapply hom_of_monos.mk, exact im.iso_obj.hom, exact im.fac }, 
  { fapply hom_of_monos.mk, exact im.iso_obj.inv, apply eq.inverse, apply iso_move_lr, 
    exact im.fac },
  exact is_prop.elim _ _, exact is_prop.elim _ _ 
end

@[hott]
def iso_to_iso_of_monos {C : Category} {c : C} (a b : subobject c) :
  (a ≅ b) -> (iso_of_monos a.is_mono b.is_mono) :=
begin 
  intro i, fapply iso_of_monos.mk, 
  { fapply iso.mk, exact i.hom.hom_obj, exact i.inv.hom_obj, 
    exact ap hom_of_monos.hom_obj i.r_inv, exact ap hom_of_monos.hom_obj i.l_inv },
  { exact i.hom.fac }
end    

@[hott]
def iso_of_monos_eqv_iso {C : Category} {c : C} (a b : subobject c) :
  (iso_of_monos a.is_mono b.is_mono) ≃ (a ≅ b) :=
begin 
  fapply equiv.mk,
  { exact iso_of_monos_to_iso a b },
  { fapply adjointify, 
    { exact iso_to_iso_of_monos a b },
    { intro i, apply hom_eq_to_iso_eq, exact is_prop.elim _ _ },
    { intro i, exact @is_prop.elim _ 
              (is_prop_iso_of_monos a.is_mono b.is_mono) _ _ } }
end  

@[hott]
def subobj_idtoiso {C : Category} {c : C} (a b : subobject c) : 
  @idtoiso _ _ a b = (iso_of_monos_eqv_iso a b).to_fun ∘ 
                     (equal_subobj_eqv_iso_mono a b).to_fun :=
begin apply eq_of_homotopy, intro p, apply hom_eq_to_iso_eq, exact is_prop.elim _ _ end                       

@[hott, instance]
def subobject_is_cat {C : Category} {c : C} : 
  is_cat (subobject c) :=
begin apply is_cat.mk, intros a b, rwr subobj_idtoiso a b, apply_instance end    

@[hott]
def subobject_Category {C : Category} (c : C) : Category :=
  Category.mk (subobject c) subobject_is_cat

@[hott]
def subobj_antisymm {C : Category} {c : C} (a b : subobject_Category c) : 
  (a ⟶ b) -> (b ⟶ a) -> (a = b) :=
begin 
  intros i j , 
  have iso_ab : a ≅ b, from 
    begin 
      fapply iso.mk, exact i, exact j, 
      exact @is_prop.elim _ (subobject_hom_is_prop b b) _ _, 
      exact @is_prop.elim _ (subobject_hom_is_prop a a) _ _ 
    end,  
  exact category.isotoid iso_ab 
end  

@[hott]
def subobj_trans {C : Category} {c : C} (a : subobject c) 
  (b : subobject a.obj) : subobject c :=
subobject.mk b.obj (b.hom ≫ a.hom) (is_mono_is_trans b.is_mono a.is_mono) 

/- The category of subobjects always has a top element. -/
@[hott]
def top_subobject {C : Category} (c : C) : subobject c := 
  subobject.mk c (𝟙 c) (isos_are_mono (id_iso c))

@[hott]
def top_subobj_prop {C : Category} {c : C} : 
  Π (a : subobject c), a ⟶ top_subobject c := 
begin intro a, fapply hom_of_monos.mk, exact a.hom, hsimp end   

/- We can define images of homomorphisms as subobjects of their codomain satisfying a 
   minimal property. Note that the factoring homomorphism is unique as the inclusion 
   homomorphism is a monomorphism. -/
@[hott]
structure cat_image {C : Category} {c d : C} (f : c ⟶ d) :=
  (subobj : subobject d)
  (fac : Σ f' : c ⟶ subobj.obj, f' ≫ subobj.hom = f)
  (univ : Π (a : subobject d), (Σ f' : c ⟶ a.obj, f' ≫ a.hom = f) -> (subobj ⟶ a))

@[hott] 
def subobject_fac_is_unique {C : Category} {c d : C} (f : c ⟶ d) 
  (a : subobject d) : Π fac₁ fac₂ : (Σ (f' : c ⟶ a.obj), f' ≫ a.hom = f), fac₁ = fac₂ :=
begin 
  intros fac₁ fac₂, fapply sigma.sigma_eq, 
  { fapply a.is_mono, exact fac₁.2 ⬝ fac₂.2⁻¹ }, 
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott, instance] 
def subobject_fac_is_prop {C : Category} {c d : C} (f : c ⟶ d) 
  (a : subobject d) : is_prop (Σ f' : c ⟶ a.obj, f' ≫ a.hom = f) :=
is_prop.mk (subobject_fac_is_unique f a)  

@[hott]
class has_image {C : Category} {c d : C} (f : c ⟶ d) :=
  (exists_im : ∥cat_image f∥)

@[hott]
def cat_image_is_unique {C : Category} {c d : C} (f : c ⟶ d) :
  Π im₁ im₂ : cat_image f, im₁ = im₂ :=
begin
  intros im₁ im₂, 
  hinduction im₁ with subobj₁ fac₁ univ₁, hinduction im₂ with subobj₂ fac₂ univ₂, 
  fapply apdd2 cat_image.mk, 
  { fapply subobj_antisymm, exact univ₁ subobj₂ fac₂, exact univ₂ subobj₁ fac₁ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
end  

@[hott, instance]
def cat_image_is_prop {C : Category} {c d : C} (f : c ⟶ d) : 
  is_prop (cat_image f) :=
is_prop.mk (cat_image_is_unique f)  

@[hott, reducible]
def hom.image {C : Category} {c d : C} (f : c ⟶ d) [has_image f] : 
  subobject d :=  
(@untrunc_of_is_trunc _ _ (cat_image_is_prop f) (has_image.exists_im f)).subobj

@[hott, reducible]
def hom_to_image {C : Category} {c d : C} (f : c ⟶ d) [has_image f] :
  c ⟶ (hom.image f).obj := 
(untrunc_of_is_trunc (has_image.exists_im f)).fac.1  

@[hott]
def hom_to_image_eq {C : Category} {c d : C} (f : c ⟶ d) [has_image f] :
  hom_to_image f ≫ (hom.image f).hom = f := 
(untrunc_of_is_trunc (has_image.exists_im f)).fac.2 

@[hott]
def hom_image_univ {C : Category} {c d : C} (f : c ⟶ d) [has_image f] :
  Π (a : subobject d) (f' : c ⟶ a.obj), f' ≫ a.hom = f -> (hom.image f ⟶ a) :=
assume a f' p, (untrunc_of_is_trunc (has_image.exists_im f)).univ a ⟨f', p⟩ 

@[hott, instance]
def subobj_has_im {C : Category} {c : C} (b : subobject c) :
  has_image b.hom :=
have im_b : cat_image b.hom, from 
  cat_image.mk b (sigma.mk (𝟙 b.obj) (is_precat.id_comp b.hom)) 
               (λ a m, hom_of_monos.mk _ _ m.1 m.2),  
has_image.mk (tr im_b)

@[hott]
def subobj_is_im {C : Category} {c : C} (b : subobject c) :
  hom.image b.hom = b := idp  

@[hott]
def im_incl {C : Category} {a b c : C} (f : a ⟶ b) (g : b ⟶ c) 
  [has_image (f ≫ g)] [has_image g] : hom.image (f ≫ g) ⟶ hom.image g :=
begin 
  fapply cat_image.univ, fapply sigma.mk, 
  { exact f ≫ hom_to_image g }, 
  { rwr is_precat.assoc, rwr hom_to_image_eq g }
end  

@[hott]
class has_images (C : Category) :=
  (has_im : Π {c d : C} (f : c ⟶ d), has_image f)

@[hott, instance]
def has_image_of_has_images {C : Category} [has_images C] {c d : C} 
  (f : c ⟶ d) : has_image f :=
has_images.has_im f

end hott