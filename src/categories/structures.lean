import sets.algebra init2 sets.axioms sets.theories categories.basic categories.limits

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv 
     hott.categories hott.categories.limits

namespace categories

/- We define multi-sorted stamdard structures on categories and prove the Structure 
   Identity Principle, following and generalizing the [HoTT-Book], Section 9.8.  -/
@[hott]
structure std_structure_on (C : Type u) [category.{v} C] :=
  (S : Set)   --the set of sorts of the structure
  (P : (S -> C) -> Type w)
  (H : Π {s t : S -> C} (α : P s) (β : P t) (f : Π (x : S), s x ⟶ t x), 
                                                                trunctype.{0} -1)
  (id_H : ∀ {s : S -> C} (α : P s), H α α (λ x : S, 𝟙 (s x)))
  (comp_H : ∀ {s t u : S -> C} (α : P s) (β : P t) (γ : P u) (f : Π x : S, s x ⟶ t x) 
              (g : Π x : S, t x ⟶ u x), 
              H α β f -> H β γ g -> H α γ (λ x : S, f x ≫ g x))
  (std : ∀ {s : S ->C} (α β : P s), 
           (H α β (λ x : S, 𝟙 (s x)) × H β α (λ x : S, 𝟙 (s x))) ≃ α = β)           

@[hott]
structure std_structure {C : Type u} [category.{v} C] (std_str : std_structure_on C) := 
  (carrier : std_str.S -> C)
  (str : std_str.P carrier)  

@[hott]
instance {C : Type u} [category.{v} C] (std_str : std_structure_on C) : 
  has_coe (std_structure std_str) (std_str.S -> C) :=
⟨λ x : std_structure std_str, x.carrier⟩  

@[hott]
def std_str_eta {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  (x : std_structure std_str) : x = std_structure.mk x.carrier x.str :=
begin hinduction x, refl end  

@[hott, instance]
def std_str_is_set {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  ∀ s : std_str.S -> C, is_set (std_str.P s) :=
assume s, 
have eq_eq : ∀ (α β : std_str.P s), is_prop (α = β), from 
  assume α β, is_trunc_equiv_closed -1 (std_str.std α β) (prod.is_trunc_prod _ _ -1),
is_trunc_succ_intro eq_eq 

@[hott, instance]
def std_str_po_is_prop {C : Type u} [category.{v} C] (std_str : std_structure_on C)
  {s t : std_str.S -> C} {α : std_str.P s} {β : std_str.P t} :
  ∀ p : s = t, is_prop (α =[p] β) :=
begin 
  intro p, hinduction p, 
  apply is_trunc_equiv_closed_rev -1 (pathover_idp _ α β), 
  exact is_prop.mk (@is_set.elim _ _ α β)
end   

/- Equalities like these should be produced automatically. -/
@[hott]
def ap_apd011_str {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {s t : std_str.S -> C} {α : std_str.P s} {β : std_str.P t} : ∀ (p : s = t) (q : α =[p] β), 
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
has_hom.mk (λ (str₁ str₂ : std_structure std_str), 
            pred_Set (λ f : to_Set (Π x : std_str.S, (str₁.carrier x ⟶ str₂.carrier x)), 
                       std_str.H (str₁.str) (str₂.str) f))

@[hott]
instance hom_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {str₁ str₂ : std_structure std_str} : 
  has_coe ↥(str₁ ⟶ str₂) (Π x : std_str.S, (str₁.carrier x ⟶ str₂.carrier x)) :=
⟨λ f : str₁ ⟶ str₂, pred_Set_map _ f⟩  

@[hott]
def hom_H {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {str₁ str₂ : std_structure std_str} :
  Π f : str₁ ⟶ str₂, std_str.H str₁.str str₂.str (↑f) :=
begin intro f, exact f.2 end              

@[hott]
def hom_eq_C_std {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {str₁ str₂ : std_structure std_str} (f g : str₁ ⟶ str₂) : 
  (f.1 = (g.1 : Π x : std_str.S, (str₁.carrier x ⟶ str₂.carrier x))) -> (f = g) :=
assume (hom_eq_C : f.1 = g.1), 
have H_eq : f.2 =[hom_eq_C; (λ f : to_Set (Π x : std_str.S, (str₁.carrier x ⟶ str₂.carrier x)), 
                       std_str.H (str₁.str) (str₂.str) f)] g.2, from 
  pathover_prop_eq _ hom_eq_C (hom_H f) (hom_H g),
calc f = ⟨f.1, f.2⟩ : (sigma.eta f)⁻¹ 
   ... = ⟨g.1, g.2⟩ : dpair_eq_dpair hom_eq_C H_eq
   ... = g : sigma.eta g 

@[hott, instance]
def std_str_cat_struct {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  category_struct (std_structure std_str) :=
category_struct.mk (λ str : std_structure std_str, 
                            ⟨λ x : std_str.S, 𝟙 (str.carrier x), std_str.id_H str.str⟩) 
  (λ (str₁ str₂ str₃ : std_structure std_str) (f : str₁ ⟶ str₂) (g : str₂ ⟶ str₃), 
     ⟨(λ x : std_str.S, (f : Π x : std_str.S, (str₁.carrier x ⟶ str₂.carrier x)) x ≫ g.1 x), 
                        std_str.comp_H str₁.str str₂.str str₃.str ↑f ↑g (hom_H f) (hom_H g)⟩) 

@[hott]
def idhom_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  (str : std_structure std_str) : ↑(𝟙 str) = λ x, 𝟙 (str.carrier x) :=
rfl  

@[hott]
def comp_hom_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C} 
  {str₁ str₂ str₃ : std_structure std_str} (f : str₁ ⟶ str₂) (g : str₂ ⟶ str₃) : 
  (f ≫ g).1 = λ x : std_str.S, f.1 x ≫ g.1 x :=
rfl  

@[hott, instance]
def std_str_precategory {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  precategory (std_structure std_str) :=
have ic : ∀ (str₁ str₂ : std_structure std_str) (f : str₁ ⟶ str₂), 𝟙 str₁ ≫ f = f, from 
begin 
  intros str₁ str₂ f, apply hom_eq_C_std _ _, rwr comp_hom_std_C, 
  apply eq_of_homotopy, intro x, hsimp 
end,
have ci : ∀ (str₁ str₂ : std_structure std_str) (f : str₁ ⟶ str₂), f ≫ 𝟙 str₂ = f, from 
begin 
  intros str₁ str₂ f, apply hom_eq_C_std _ _, rwr comp_hom_std_C, 
  apply eq_of_homotopy, intro x, hsimp 
end,
have as : ∀ (str₁ str₂ str₃ str₄: std_structure std_str) (f : str₁ ⟶ str₂) (g : str₂ ⟶ str₃) 
            (h : str₃ ⟶ str₄), (f ≫ g) ≫ h = f ≫ (g ≫ h), from 
begin 
  intros x y z w f g h, apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, 
  apply eq_of_homotopy, intro x, hsimp 
end,
precategory.mk ic ci as 

/- We prove the Structure Identity principle by splitting up the equivalence making the 
   precategory into a category into 5 equivalence and by showing that the composition of the
   5 equivalence maps is `idtoiso`. 

   The first equivalence introduces the structure components in standard structures equalities. -/
@[hott]
def std_str_comp_eq {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {str₁ str₂ : std_structure std_str} :
  (str₁ = str₂) ≃ 
          (std_structure.mk str₁.carrier str₁.str = std_structure.mk str₂.carrier str₂.str) :=
begin hinduction str₁ with s α, hinduction str₂ with t β, exact equiv.rfl end

/- The second equivalence is the eta principle for standard structures equalities. -/
@[hott]
def std_str_eq_eta {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {s t : std_str.S -> C} {α : std_str.P s} {β : std_str.P t} :
  (std_structure.mk s α = std_structure.mk t β) ≃ Σ (p : s = t), α =[p] β :=
let str₁ := std_structure.mk s α, str₂ := std_structure.mk t β,
    f := λ p : str₁ = str₂, @dpair (s = t) (λ p : s = t, α =[p] β) 
         (ap std_structure.carrier p : s = t) 
         (pathover_ap std_str.P std_structure.carrier (apd std_structure.str p)),
    g := λ pq : Σ (p : s = t), α =[p] β, apd011 std_structure.mk pq.1 pq.2 in                         
have rinv : ∀ pq : Σ (p : s = t), α =[p] β, f (g pq) = pq, from 
  assume pq,
  have pq_1 : (f (g pq)).1 = pq.1, from 
    calc (f (g pq)).1 = ap std_structure.carrier (apd011 std_structure.mk pq.1 pq.2) : rfl
         ... = pq.1 : ap_apd011_str pq.1 pq.2,
  have pq_2 : (f (g pq)).2 =[pq_1; λ p : s = t, α =[p] β] pq.2, from po_proofs pq_1 _ _,
  calc f (g pq) = ⟨(f (g pq)).1, (f (g pq)).2⟩ : sigma.eta (f (g pq))
       ... = ⟨pq.1, pq.2⟩ : apd011 sigma.mk pq_1 pq_2
       ... = pq : sigma.eta pq,
have linv : ∀ p : str₁ = str₂, g (f p) = p, from 
  assume p,
  have qx : std_str_eta str₁ = idp, from rfl,
  calc g (f p) = apd011 std_structure.mk (ap std_structure.carrier p) (f p).2 : rfl
       ... = (std_str_eta str₁)⁻¹ ⬝ p ⬝ (std_str_eta str₂) : apd011_ap_str p
       ... = p : by rwr qx; rwr idp_inv; rwr idp_con p; rwr con_idp p,
equiv.mk f (adjointify f g rinv linv)    

/- The third equivalence exchanges equalities and isomorphisms. -/
@[hott]
def strpair_id_to_iso {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {s t : std_str.S -> C} {α : std_str.P s} {β : std_str.P t} :
  (Σ (p : s = t), α =[p] β) ≃ (Σ (f : Π x, s x ≅ t x), std_str.H α β (λ x, (f x).hom) and 
                                                        std_str.H β α (λ x, (f x).inv)) :=
begin                                                        
  let str₁ := std_structure.mk s α, let str₂ := std_structure.mk t β, 
  have po_hom : Π (p : s = t) (q : α =[p] β), std_str.H α β (λ x, (idtoiso (ap10 p x)).hom) and 
                                              std_str.H β α (λ x, (idtoiso (ap10 p x)).inv), from 
  begin 
    intros p q, hinduction p, 
    have q' : α = β, from eq_of_pathover_idp q, 
    have r : (λ x : std_str.S, (idtoiso (ap10 (@idp _ s) x)).hom) = 
              λ x : std_str.S, 𝟙 (s x), from rfl,
    have r' : (λ x : std_str.S, (idtoiso (ap10 (@idp _ s) x)).inv) = 
               λ x : std_str.S, 𝟙 (s x), from rfl,         
    rwr r, rwr r', rwr <- q', exact (std_str.id_H α, std_str.id_H α) 
  end,
  have idtoiso_hom_po : ∀ p : s = t, std_str.H α β (λ x, (idtoiso (ap10 p x)).hom) and 
                            std_str.H β α (λ x, (idtoiso (ap10 p x)).inv) -> α =[p] β, from
    begin intros p H, hinduction p, apply pathover_idp_of_eq, exact std_str.std α β H end,
  have hom_po : Π (f : Π x, s x ≅ t x), (std_str.H α β (λ x, (f x).hom) and 
                  std_str.H β α (λ x, (f x).inv)) -> 
                  α =[eq_of_homotopy (λ x, category.isotoid (f x))] β, from 
    assume f H,
    have r : f = λ x, idtoiso (ap10 (eq_of_homotopy (λ x, category.isotoid (f x))) x), from
      begin 
        apply eq_of_homotopy, intro x, change f x = idtoiso (apd10 _ x),
        rwr apd10_eq_of_homotopy, change _ = idtoiso (idtoiso⁻¹ᶠ (f x)), 
        rwr category.idtoiso_rinv (f x) 
      end, 
    begin 
      apply idtoiso_hom_po, 
      rwr <- eq_of_homotopy (λ x, ap iso.hom (apd10 r x)), 
      rwr <- eq_of_homotopy (λ x, ap iso.inv (apd10 r x)), exact H 
    end, 
  let F := λ (pq : Σ (p : s = t), α =[p] β), @dpair (Π x, s x ≅ t x) 
    (λ f : Π x, s x ≅ t x, std_str.H α β (λ x, (f x).hom) and std_str.H β α (λ x, (f x).inv)) 
    (λ x, idtoiso (ap10 pq.1 x)) (po_hom pq.1 pq.2),  
  let G := λ iso_H : (Σ (f : Π x, s x ≅ t x), std_str.H α β (λ x, (f x).hom) and 
                       std_str.H β α (λ x, (f x).inv)), @dpair (s = t) (λ p : s = t, α =[p] β) 
                (eq_of_homotopy (λ x, category.isotoid (iso_H.1 x))) (hom_po iso_H.1 iso_H.2),
  have rinv : ∀ iso_H, F (G iso_H) = iso_H, from 
  begin
    intro iso_H, fapply sigma_eq,
    { apply eq_of_homotopy, intro x, 
      change idtoiso (apd10 _ x) = iso_H.1 x, rwr apd10_eq_of_homotopy,
      change idtoiso (idtoiso⁻¹ᶠ (iso_H.1 x)) = iso_H.1 x,
      exact category.idtoiso_rinv (iso_H.1 x) },
    { apply pathover_of_eq_tr, exact is_prop.elim _ _ }
  end,
  have linv : ∀ (pq : Σ (p : s = t), α =[p] β), G (F pq) = pq, from 
  begin
    intro pq, hinduction pq.1 with h,
    fapply sigma_eq,
    { change (eq_of_homotopy (λ x, idtoiso⁻¹ᶠ (idtoiso (apd10 pq.1 x)))) = _,  
      have r : Π x, apd10 pq.1 x = @idp _ (s x), from begin intro x, rwr h end, 
      have q : (λ x, idtoiso⁻¹ᶠ (idtoiso (apd10 pq.1 x))) = λ x, (@idp _ (s x)), from 
      begin 
        apply eq_of_homotopy, intro x, change idtoiso⁻¹ᶠ (idtoiso (apd10 pq.1 x)) = _,
        rwr r x, rwr category.idtoiso_linv ((@idp _ (s x)))
      end,  
      rwr q, rwr h, rwr eq_of_homotopy_idp }, 
    { apply pathover_of_eq_tr, exact is_prop.elim _ _ }, 
  end,                                                             
  exact equiv.mk F (adjointify F G rinv linv) 
end

/- The fourth equivalence splits up equalities of standard structure isomorphisms. -/
@[hott]
def iso_std_C {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {str₁ str₂ : std_structure std_str} (F : str₁ ≅ str₂) : Π x, str₁.carrier x ≅ str₂.carrier x :=
let f := (F.hom : str₁ ⟶ str₂).1, g := F.inv.1 in
have rinv : Π x, (g x) ≫ (f x) = 𝟙 (str₂.carrier x), 
  begin intro x, change (F.inv ≫ F.hom).1 x = _, rwr F.r_inv end,
have linv : Π x, (f x) ≫ (g x) = 𝟙 (str₁.carrier x), 
  begin intro x, change (F.hom ≫ F.inv).1 x = _, rwr F.l_inv end, 
assume x, iso.mk (f x) (g x) (rinv x) (linv x)  

@[hott]
def str_iso_eq_comp {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {s t : std_str.S -> C} {α : std_str.P s} {β : std_str.P t} :
  (Σ (f : Π x, s x ≅ t x), std_str.H α β (λ x, (f x).hom) and std_str.H β α (λ x, (f x).inv)) ≃ 
  (std_structure.mk s α ≅ std_structure.mk t β) :=
begin
  let str₁ := std_structure.mk s α, let str₂ := std_structure.mk t β,
  fapply equiv.mk,
  /- We define `F : (Σ (f : Π x, s x ≅ t x), std_str.H α β (λ x, (f x).hom) and`
                                            `std_str.H β α (λ x, (f x).inv)) -> (str₁ ≅ str₂)`. -/
  { intro iso_H, 
    fapply iso.mk,
    { exact ⟨λ x, (iso_H.1 x).hom, iso_H.2.1⟩ },
    { exact ⟨λ x, (iso_H.1 x).inv, iso_H.2.2⟩ },
    { apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, hsimp, 
      apply eq_of_homotopy, intro x, hsimp, rwr (iso_H.1 x).r_inv },
    { apply hom_eq_C_std _ _, repeat { rwr comp_hom_std_C }, hsimp, 
      apply eq_of_homotopy, intro x, hsimp, rwr (iso_H.1 x).l_inv } },
  { fapply adjointify,
    /- Now we define `G : (str₁ ≅ str₂) -> (Σ (f : Π x, s x ≅ t x), std_str.H α β (λ x, (f x).hom) and`
                                            `std_str.H β α (λ x, (f x).inv))`. -/
    { intro f, 
      fapply sigma.mk,
      { exact iso_std_C f },
      { exact (f.hom.2, f.inv.2) } },
    /- `r_inv : ∀ f : str₁ ≅ str₂, F (G f) = f` -/  
    { intro f,
      apply hom_eq_to_iso_eq, apply hom_eq_C_std _ _, 
      hsimp, refl },
    /- `l_inv : ∀ iso_H : (Σ (f : Π x, s x ≅ t x), std_str.H α β (λ x, (f x).hom) and`
                                            `std_str.H β α (λ x, (f x).inv)), G (F iso_H)) = iso_H` -/  
    { intro iso_H, 
      fapply sigma_eq, 
      { apply eq_of_homotopy, intro x, apply hom_eq_to_iso_eq, refl },
      { apply pathover_of_eq_tr, exact is_prop.elim _ _ } } }
end    

/- The last equivalence introduces the structure components in standard structures isomorphies. -/
@[hott]
def std_str_comp_iso {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {str₁ str₂ : std_structure std_str} :
  (str₁ ≅ str₂) ≃ (std_structure.mk str₁.carrier str₁.str ≅ std_structure.mk str₂.carrier str₂.str) :=
begin hinduction str₁ with s α, hinduction str₂ with t β, exact equiv.rfl end

/- Finally, we show that the composition of the five equivalences is `idtoiso`. -/
@[hott]
def comp_eqv_idtoiso {C : Type u} [category.{v} C] {std_str : std_structure_on C}
  {str₁ str₂ : std_structure std_str} (p : str₁ = str₂) :
        (std_str_comp_iso.to_fun⁻¹ᶠ (str_iso_eq_comp.to_fun (strpair_id_to_iso.to_fun 
                            (std_str_eq_eta.to_fun (std_str_comp_eq.to_fun p))))) = idtoiso p :=                            
begin
  hinduction p, hinduction str₁ with s α,
  let str := std_structure.mk s α,
  have p₁ : std_str_comp_eq.to_fun (refl str) = refl str, from rfl,
  have p₂ : std_str_eq_eta.to_fun (refl str) = ⟨refl s, idpo⟩, from rfl,
  have p₃ : strpair_id_to_iso.to_fun ⟨refl s, idpo⟩ = 
            ⟨λ x, id_is_iso (s x), (std_str.id_H α, std_str.id_H α)⟩, from rfl,
  have p₄ : str_iso_eq_comp.to_fun ⟨λ x, id_is_iso (s x), (std_str.id_H α, std_str.id_H α)⟩ = id_is_iso str,
    by apply hom_eq_to_iso_eq; refl,         
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

/- The forgetful functor from a category of multi-sorted standard structures to the underlying 
   category (which has products). -/
@[hott]
def forget_str {C : Type u} [category.{v} C] [has_products C] (std_str : std_structure_on C) :
  (std_structure std_str) ⥤ C :=
begin
  fapply functor.mk,  
  { intro str, exact @pi_obj _ _ _ str.carrier (has_product_of_has_products str.carrier) },  
                                                                          -- map of objects
  { intros str₁ str₂ f, exact pi.lift (λ x, (pi.π str₁.carrier x) ≫ f.1 x) },  
                                                                         -- map of morphisms
  { intro str, change pi.lift (λ (x : ↥(std_str.S)), pi.π str.carrier x ≫ 𝟙 (str.carrier x)) = _, 
    have p : (λ x, pi.π str.carrier x ≫ 𝟙 (str.carrier x)) = 
              λ x, 𝟙 (∏ str.carrier) ≫ pi.π str.carrier x, from
      begin apply eq_of_homotopy, intro x, hsimp end, 
    rwr p, apply eq.inverse, apply pi.hom_is_lift },  -- preserves identity morphisms
  { intros str₁ str₂ str₃ f g, 
    change pi.lift (λ x, pi.π str₁.carrier x ≫ (f ≫ g).fst x) = 
           pi.lift (λ x, pi.π str₁.carrier x ≫ f.fst x) ≫ 
                                                  pi.lift (λ x, pi.π str₂.carrier x ≫ g.fst x),
    have p : (λ x, pi.π str₁.carrier x ≫ (f ≫ g).fst x) = 
             (λ x, pi.lift (λ x, pi.π str₁.carrier x ≫ f.1 x) ≫ pi.π str₂.carrier x ≫ (g.1 x)), from 
    begin 
      apply eq_of_homotopy, intro x, change pi.π str₁.carrier x ≫ (f.1 x) ≫ (g.1 x) = _,
      rwr <- precategory.assoc, 
      change _ = pi.lift (λ x, pi.π str₁.carrier x ≫ f.fst x) ≫ pi.π str₂.carrier x ≫ g.fst x, 
      rwr <- precategory.assoc, rwr pi.lift_π_eq
    end,                       
    rwr p, rwr pi.lift_fac (pi.lift (λ x, pi.π str₁.carrier x ≫ f.1 x)) 
                           (λ x, pi.π str₂.carrier x ≫ g.1 x) }  
                           -- preserves compositions of morphisms 
end 

/- The forgetful functor is faithful. -/
@[hott]
def forget_is_faithful {C : Type u} [category.{v} C] [has_products C] 
  (std_str : std_structure_on C) : is_faithful_functor _ _ (forget_str std_str) :=
begin 
  intros str₁ str₂ f₁ f₂ p, fapply sigma.sigma_eq, 
  { apply eq_of_homotopy, intro x, sorry },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end  

/- The forgetful functor composed with a functor to a category of standard structures -/
@[hott]
def forget {J : Type.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] [has_products C]
  {std_str : std_structure_on C} (F : J ⥤ std_structure std_str) : J ⥤ C :=
F ⋙ (forget_str std_str)


/- A criterion for a category of standard structures over a category with limits to have limits:
   - The limit cone of the underlying functor of a shape carries a structure.
   - The leg morphisms of this limit cone respect the structures.
   - The lift morphisms to this limit cone respect the structures. 
   
   We first need to construct the underlying cone of a cone in the category of structures. -/
@[hott, reducible]
def str_cone_to_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  [has_products C] {std_str : std_structure_on C} {F : J ⥤ (std_structure std_str)} 
  (s : cone F) : cone (forget F) :=
begin 
  fapply cone.mk, 
  { exact s.X.1 },  -- vertex
  { fapply nat_trans.mk,
    { intro j, exact (s.π.app j).1 },  --transformation of objects
    { intros j k f, hsimp, 
      change (s.π.app k).1 = (s.π.app j).1 ≫ (F.map f).1, rwr <- comp_hom_std_C _ _,
      rwr <- ap sigma.fst (s.π.naturality f), hsimp } }  --naturality
end    

/- We define the structure data of a limit cone for all limit cones of the underlying
   category at once, because we can change then easily to the most fitting construction. -/
@[hott]
structure limit_cone_str_data {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [category.{v} C] [has_products C] {std_str : std_structure_on C} 
  {F : J ⥤ (std_structure std_str)} (lc : limit_cone (forget F)) :=
(lc_str : std_str.P (lc.cone.X)) 
(lc_legs_H : Π (j : J), std_str.H lc_str ((F.obj j).str) (lc.cone.π.app j))
(lift_H : Π (s : cone F), std_str.H s.X.str lc_str (lc.is_limit.lift (str_cone_to_cone s)))

@[hott]
def str_limit_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [category.{v} C] [has_products C] {std_str : std_structure_on C} 
  {F : J ⥤ (std_structure.{v u w} std_str)} (lc : limit_cone (forget F))
  (lcd : limit_cone_str_data lc) : limit_cone F :=
begin 
  fapply limit_cone.mk, 
  { fapply cone.mk, -- the limit cone 
    { exact std_structure.mk lc.cone.X lcd.lc_str },
    { fapply nat_trans.mk, 
      { intro j, 
        exact ⟨lc.cone.π.app j, lcd.lc_legs_H j⟩ },
      { intros j k f, apply hom_eq_C_std, rwr comp_hom_std_C,  
        exact lc.cone.π.naturality f } } },
  { fapply is_limit.mk, -- the limit cone is a limit
    { intro s, 
      exact ⟨lc.is_limit.lift (str_cone_to_cone s), lcd.lift_H s⟩ },
    { intros s j, apply hom_eq_C_std, rwr comp_hom_std_C, hsimp, 
      exact lc.is_limit.fac (str_cone_to_cone s) j },
    { intros s m fac_m, apply hom_eq_C_std, hsimp, 
      have fac_m1 : ∀ j : J, m.1 ≫ (lc.cone.π.app j) = 
                                                   (str_cone_to_cone s).π.app j, from 
        assume j, 
        calc m.1 ≫ (lc.cone.π.app j) = (s.π.app j).1 : ap sigma.fst (fac_m j)
             ... = (str_cone_to_cone s).π.app j : rfl,
      exact lc.is_limit.uniq (str_cone_to_cone s) m.1 fac_m1 } }
end                

@[hott]
def str_has_limit {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [category.{v} C] [has_products C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  (F : J ⥤ (std_structure std_str)) 
  (lcd : limit_cone_str_data (get_limit_cone (forget F))) : has_limit F :=
has_limit.mk (str_limit_cone (get_limit_cone (forget F)) lcd)                                           

@[hott, instance]
def std_structure_has_limits_of_shape {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [category.{v} C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  (lcd_F : Π F : J ⥤ (std_structure std_str), limit_cone_str_data (get_limit_cone (forget F))) : 
  has_limits_of_shape J (std_structure std_str) :=
has_limits_of_shape.mk (λ F, str_has_limit F (lcd_F F))


open signature

/- We define structures of a gven signature in a category `C` with products. -/
@[hott]  
structure Sig_structure_on (sign : fo_signature) {C : Type u} [category.{v} C] :=
  ( car : sign.sorts -> C )
  
  ( ops : ∀ o : sign.ops, ((sign.ops_arity o) -> carrier) -> carrier )
  ( rels : ∀ r : sign.rels, ((sign.rels_arity r) -> carrier) -> trunctype.{0} -1 )

/- The following three lemmas should be produced automatically. -/
@[hott]
def Ω_str_eq {sign : fo_signature} {carrier : Set} 
  {Ω_str₁ Ω_str₂ : Ω_structure_on sign carrier} : 
  (Ω_str₁.ops = Ω_str₂.ops) -> (Ω_str₁.rels = Ω_str₂.rels) -> (Ω_str₁ = Ω_str₂) :=
begin
  intros p_ops p_rels, 
  hinduction Ω_str₁ with ops₁ rels₁, hinduction Ω_str₂ with ops₂ rels₂,
  exact ap011 Ω_structure_on.mk p_ops p_rels
end    

@[hott]
def Ω_str_eq_eta {sign : fo_signature} {carrier : Set} 
  {Ω_str₁ Ω_str₂ : Ω_structure_on sign carrier} (p : Ω_str₁ = Ω_str₂) :
  Ω_str_eq (ap Ω_structure_on.ops p) (ap Ω_structure_on.rels p) = p := 
begin
  hinduction p, hinduction Ω_str₁, reflexivity
end    

@[hott, instance]
def is_set_Ω_structure_on (sign : fo_signature) (carrier : Set) : 
  is_set (Ω_structure_on sign carrier) :=
begin
  fapply is_set.mk, intros Ω_str₁ Ω_str₂ p q, 
  rwr <- Ω_str_eq_eta p, rwr <- Ω_str_eq_eta q,
  apply ap011 Ω_str_eq,
  apply is_set.elim, apply is_set.elim
end    

@[hott]
structure is_Ω_structure_hom {sign : fo_signature} {A B : Set.{u}} 
  (Ω_A : Ω_structure_on sign A) (Ω_B : Ω_structure_on sign B) (h : A -> B) :=
( ops_pres : ∀ (o : sign.ops) (x : (sign.ops_arity o) -> A), 
                                                     h (Ω_A.ops o x) = Ω_B.ops o (h ∘ x) ) 
( rels_pres : ∀ (r : sign.rels) (x : (sign.rels_arity r) -> A), 
                                                     Ω_A.rels r x -> Ω_B.rels r (h ∘ x) )                                                       

@[hott, instance]
def is_prop_is_Ω_Structure_hom {sign : fo_signature} {A B : Set.{u}} 
  (Ω_A : Ω_structure_on sign A) (Ω_B : Ω_structure_on sign B) (h : A -> B) : 
  is_prop (is_Ω_structure_hom Ω_A Ω_B h) :=
begin
  apply is_prop.mk, intros strh₁ strh₂, 
  hinduction strh₁ with ops_pres₁ rels_pres₁, hinduction strh₂ with ops_pres₂ rels_pres₂,
  fapply ap011 is_Ω_structure_hom.mk,
  { exact is_prop.elim _ _ },
  { exact is_prop.elim _ _ }
end    

@[hott]
def std_str_of_Ω_str (sign : fo_signature) : std_structure_on Set :=
begin
  fapply std_structure_on.mk,
  { exact λ S : Set, Ω_structure_on sign S },
  { intros S T Ω_Str_S Ω_Str_T h, 
    exact prop_resize (to_Prop (@is_Ω_structure_hom sign _ _ Ω_Str_S Ω_Str_T h)) },
  { intros A Ω_str_A, apply prop_to_prop_resize, fapply is_Ω_structure_hom.mk, 
    { intros o x, refl },
    { intros r x a, exact a } },
  { intros A B C Ω_str_A Ω_str_B Ω_str_C f g p_Ω_hom_f p_Ω_hom_g, 
    apply prop_to_prop_resize, fapply is_Ω_structure_hom.mk, 
    { intros o x, change g (f (Ω_str_A.ops o x)) = Ω_str_C.ops o ((f ≫ g) ∘ x), 
      rwr (prop_resize_to_prop p_Ω_hom_f).ops_pres o x,
      rwr (prop_resize_to_prop p_Ω_hom_g).ops_pres o (f ∘ x) },
    { intros r x a, change ↥(Ω_str_C.rels r (g ∘ (f ∘ x))), 
      apply (prop_resize_to_prop p_Ω_hom_g).rels_pres r (f ∘ x), 
      apply (prop_resize_to_prop p_Ω_hom_f).rels_pres r x, exact a } },
  { intros A Ω_str_A₁ Ω_str_A₂, fapply equiv.mk, 
    { intro Ω_str_homs, 
      hinduction Ω_str_A₁ with ops₁ rels₁, hinduction Ω_str_A₂ with ops₂ rels₂, 
      fapply ap011 Ω_structure_on.mk, 
      { apply eq_of_homotopy, intro o, apply eq_of_homotopy, intro x, 
        exact (prop_resize_to_prop Ω_str_homs.1).ops_pres o x },
      { apply eq_of_homotopy, intro r, apply eq_of_homotopy, intro x, 
        apply prop_iff_eq, 
        { intro rx₁, apply (prop_resize_to_prop Ω_str_homs.1).rels_pres r x, exact rx₁ },
        { intro rx₂, apply (prop_resize_to_prop Ω_str_homs.2).rels_pres r x, exact rx₂ } } },
    { fapply adjointify, 
      { intro Ω_str_eq, rwr Ω_str_eq, 
        have Ω_str_id : is_Ω_structure_hom Ω_str_A₂ Ω_str_A₂ (𝟙 A), from 
        begin 
          apply is_Ω_structure_hom.mk, 
          { intros o x, refl },
          { intros r x rx, exact rx }
        end,
        exact ⟨prop_to_prop_resize Ω_str_id, prop_to_prop_resize Ω_str_id⟩ },
      { intro b, exact @is_set.elim _ _ Ω_str_A₁ Ω_str_A₂ _ b },
      { intro a, exact is_prop.elim _ _ } } }
end  

@[hott]
def Ω_structure (sign : fo_signature) :=
  std_structure (std_str_of_Ω_str sign)

@[hott, instance]
def Ω_sign_str_precategory (sign : fo_signature) : 
  precategory (Ω_structure sign) := 
std_str_precategory (std_str_of_Ω_str sign)

@[hott, instance]
def Ω_str_precategory (sign : fo_signature) : 
  precategory (Ω_structure sign) := 
std_str_precategory (std_str_of_Ω_str sign)

@[hott, instance]
def Ω_sign_str_category (sign : fo_signature) : 
  category (Ω_structure sign) := 
structure_identity_principle (std_str_of_Ω_str sign)

/- The category of Ω-structures on sets having a given signature is usually too large to
   capture algebraic structures: These require that particular relations involving the
   operations are true for all possible arguments. 
   
   By prescribing logical equivalences of the signature relations to such relations and
   and requesting that they are always true we can define a predicate on the objects 
   of the Ω-structure category that gives a full subcategory. -/
@[hott]
structure signature_laws (sign : fo_signature) :=
  (pred : Π (S : Ω_structure sign) (r : sign.rels) 
            (args : (sign.rels_arity r) -> S.carrier), trunctype.{0} -1)
  (funct : Π {S T : Ω_structure sign} (f : S ⟶ T) (r : sign.rels) 
            (args : (sign.rels_arity r) -> S.carrier), 
            pred S r args -> pred T r (↑f ∘ args))  
  (ops_dep : Π {S T : Ω_structure sign} (f : S ⟶ T), 
               @is_set_bijective T.carrier S.carrier f -> 
               ∀ (r : sign.rels) (args : (sign.rels_arity r) -> S.carrier), 
               pred S r args <-> pred T r (↑f ∘ args))                  

@[hott]
def Ω_structure_laws_pred {sign : fo_signature} (P : signature_laws sign) : 
  Ω_structure sign -> trunctype.{0} -1 :=
begin  
intro S, 
exact prop_resize 
      (to_Prop (∀ r args, (S.str.rels r args).carrier <-> (P.pred S r args)) and
       to_Prop (∀ r args, is_true (P.pred S r args)))
end                        

@[hott]
def Ω_str_subtype {sign : fo_signature} (P : signature_laws sign) := 
  sigma.subtype (λ S : Ω_structure sign, Ω_structure_laws_pred P S)

@[hott, instance]
def Ω_str_subtype_category {sign : fo_signature} (P : signature_laws sign) : 
  category (Ω_str_subtype P) :=
full_subcat_on_subtype (Ω_structure_laws_pred P)  

/- A Subset of the underlying set of an Ω-structure inherit the structure of the 
   Ω-structure if the operations are closed on the subset. -/
@[hott]
def ops_closed {sign : fo_signature} {S : Ω_structure sign} (R : Subset S.carrier) :=
  ∀ (o : sign.ops) (args : (sign.ops_arity o) -> S.carrier), 
    (∀ i : sign.ops_arity o, args i ∈ R) -> S.str.ops o args ∈ R 

@[hott]
def str_subobject {sign : fo_signature} {S : Ω_structure sign} {R : Subset S.carrier}
  (oc : ops_closed R) : Ω_structure sign :=
begin
  fapply std_structure.mk,
  { exact pred_Set R },
  { fapply Ω_structure_on.mk, 
    { intros o x, exact ⟨S.str.ops o (sigma.fst ∘ x), oc o (sigma.fst ∘ x) (λ i, (x i).2)⟩ },
    { intros r x, exact S.str.rels r (sigma.fst ∘ x) } }
end    

/- `str_subobject` is not the only structure on a subset `R` that is closed under the 
   Ω-operations on a set `S` and is compatible with the subset embedding: There may be 
   relations on elements in `R` in the Ω-structure on `S` that do not hold in the 
   Ω-structure on `R`. But `str_subobject` is terminal among all those structures. -/
@[hott]
def str_subobject_comp {sign : fo_signature} {S : Ω_structure sign} 
  {R : Subset S.carrier} (oc : ops_closed R) : 
  (std_str_of_Ω_str sign).H (str_subobject oc).str S.str (pred_Set_map R) :=
begin
  apply prop_to_prop_resize, apply is_Ω_structure_hom.mk,
  { intros o x, refl },
  { intros r x rx, exact rx }
end    

@[hott]
def terminal_str_on_subobj {sign : fo_signature} {S : Ω_structure sign} 
  {R : Subset S.carrier} (oc : ops_closed R) : 
  ∀ R_str : Ω_structure_on sign (pred_Set R), 
    (std_str_of_Ω_str sign).H R_str S.str (pred_Set_map R) ->
    (std_str_of_Ω_str sign).H R_str (str_subobject oc).str (𝟙 (pred_Set R)) :=
begin
 let substr := (str_subobject oc).str, 
 intros R_str R_str_comp, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
 { intros o x, change R_str.ops o x = substr.ops o x, apply pred_Set_map_is_inj, 
   rwr (prop_resize_to_prop R_str_comp).ops_pres o x },
 { intros r x rx, change ↥(substr.rels r x), 
   exact (prop_resize_to_prop R_str_comp).rels_pres r x rx }
end                              

/- The induced structure on a subset of an Ω-structured set closed under the 
   structure operations does not necessarily satisfy the laws of a predicate if the 
   laws are satisfied by the structured set.
   
   But this is the case if the laws are left-exact. -/
@[hott]
def left_exact_sign_laws {sign : fo_signature} (P : signature_laws sign)
  {S : Ω_structure sign} (R : Subset S.1) (oc_R : ops_closed R) := Π (r : sign.rels) 
    (args : (sign.rels_arity r) -> (pred_Set R).carrier), 
    (P.pred S r ((pred_Set_map R) ∘ args) -> P.pred (str_subobject oc_R) r args)  

@[hott]
def law_str_subset {sign : fo_signature} {P : signature_laws sign} {S : Ω_str_subtype P}
  (R : Subset S.1.1) (oc_R : ops_closed R) 
  (le_laws : @left_exact_sign_laws sign P S.1 R oc_R) : 
  Ω_str_subtype P :=
begin
  fapply sigma.mk,
  { exact str_subobject oc_R },
  { change ↥(Ω_structure_laws_pred P (str_subobject oc_R)),
    apply prop_to_prop_resize, apply prod.mk, 
    { intros r args, apply prod.mk, 
      { intro so_rel, apply le_laws r args,
        apply ((prop_resize_to_prop S.2).1 r (((pred_Set_map R)) ∘ args)).1, 
        assumption },
      { intro so_P, apply ((prop_resize_to_prop S.2).1 r (((pred_Set_map R)) ∘ args)).2, 
        apply ((prop_resize_to_prop S.2).2 r (((pred_Set_map R)) ∘ args)).2, 
        exact true.intro } },
    { intros r args, apply prod.mk, 
      { intro so_P, exact true.intro },
      { intro t, apply le_laws r args,
        apply ((prop_resize_to_prop S.2).2 r (((pred_Set_map R)) ∘ args)).2,
        assumption } } }
end

/- Ω-structured sets have all limits because the Ω-structure on sections is induced by 
   the Ω-structure on the sets in the diagram. -/
@[hott]
def Ω_str_on_limit_cone {J : Set.{u'}} [precategory.{v'} J] {sign : fo_signature} 
  (F : J ⥤ (Ω_structure sign)) : limit_cone_str_data (set_limit_cone (forget F)) :=
begin 
  fapply limit_cone_str_data.mk,
  { fapply Ω_structure_on.mk, 
    { intros o x, fapply dpair, 
      { intro j, 
        exact (F.obj j).str.ops o (((set_limit_cone (forget F)).cone.π.app j) ∘ x) },
      { apply prop_to_prop_resize, intros j k f, 
        change _ = (F.obj k).str.ops o ((set_limit_cone (forget F)).cone.π.app k ∘ x), 
        rwr <- cone.fac (set_limit_cone (forget F)).cone f, 
        exact (prop_resize_to_prop (hom_H (F.map f))).ops_pres o _ } },
    { intros r x, exact prop_resize (to_Prop (Π j : J, 
           (F.obj j).str.rels r (((set_limit_cone (forget F)).cone.π.app j) ∘ x))) } },
  { intro j, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
    { intros o x, refl },
    { intros r x limit_rel, exact prop_resize_to_prop limit_rel j } },
  { intro s, apply prop_to_prop_resize, apply is_Ω_structure_hom.mk, 
    { intros o x, fapply sigma.sigma_eq, 
      { apply eq_of_homotopy, intro j,
        change (s.π.app j).1 (s.X.str.ops o x) = (F.obj j).str.ops o ((s.π.app j).1 ∘ x),
        rwr (prop_resize_to_prop (s.π.app j).2).ops_pres },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
    { intros r x s_rel, exact prop_to_prop_resize 
                (λ j : J, (prop_resize_to_prop (s.π.app j).2).rels_pres r x s_rel) } }
end

@[hott]
def Ω_str_limit_cone {J : Set.{u'}} [precategory.{v'} J] {sign : fo_signature} 
  (F : J ⥤ (Ω_structure sign)) : limit_cone F :=
str_limit_cone (set_limit_cone (forget F)) (Ω_str_on_limit_cone F)  

@[hott, instance]
def Ω_str_has_limit {J : Set} [precategory J] {sign : fo_signature} 
  (F : J ⥤ (Ω_structure sign)) : has_limit F :=
has_limit.mk (Ω_str_limit_cone F)

@[hott, instance]
def Ω_str_has_limits_of_shape (J : Set) [precategory J] (sign : fo_signature) : 
  has_limits_of_shape J (Ω_structure sign) :=
  has_limits_of_shape.mk (λ F, Ω_str_has_limit F)     

@[hott, instance]
def Ω_str_has_products (sign : fo_signature) : has_products (Ω_structure sign) :=
  ⟨λ J : Set, Ω_str_has_limits_of_shape (discrete J) sign⟩

@[hott, instance]
def Ω_str_has_product {J : Set} {sign : fo_signature} (f : J -> (Ω_structure sign)) : 
  has_product f :=
Ω_str_has_limit (discrete.functor f)


@[hott, instance]
def subcat_has_product {J : Set} {sign : fo_signature} (f : J -> (Ω_structure sign)) : 
  has_product f :=
Ω_str_has_limit (discrete.functor f)

/- A subtype of Ω-structures is closed under taking limits. -/
@[hott]
def Ω_str_subtype_is_limit_closed {J : Set} [precategory J] {sign : fo_signature} 
  (P : signature_laws sign) (F : J ⥤ Ω_str_subtype P) : 
  limit_closed_subtype (Ω_structure_laws_pred P) F :=
begin
  intro lc, apply prop_to_prop_resize, apply prod.mk,
  { intros r x, apply prod.mk, 
    { intro lc_rel_r_x, sorry },
    { sorry } },
  { sorry }
end  

end categories

end hott