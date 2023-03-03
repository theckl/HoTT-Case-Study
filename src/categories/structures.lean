import sets.algebra init2 sets.axioms sets.theories categories.basic categories.limits

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.sigma hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv 
     hott.categories hott.categories.limits

namespace categories

/- We define multi-sorted standard structures on categories and prove the Structure 
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
   product category, with one object of the underlying category as a factor for each sort. 
   
   Even if the underlying category of the standard structure has products, the forgetful 
   functor should not map to the product of the objects corresponding to the sorts: The 
   forgetful functor may not be faithful, as it's not clear how to get back the component 
   morphisms from the morphisms between products - this only works if projections are epic, for
   example if the category has a zero = initial + terminal objects. But that's not the case 
   already for sets.

   The product category is implemented as the functor category from the discrete set of sorts 
   to the underlying category. -/
@[hott]
def forget_str {C : Type u} [category.{v} C] (std_str : std_structure_on C) :
  (std_structure std_str) ⥤ ((discrete std_str.S) ⥤ C) :=
begin
  fapply functor.mk,  
  { intro str, exact discrete.functor str.carrier }, -- map of objects
  { intros str₁ str₂ f, exact discrete.nat_trans (λ s, f.1 s) }, -- map of morphisms
  { intro str₁, apply nat_trans_eq, refl },  -- preserves identity morphisms
  { intros str₁ str₂ str₃ f g, apply nat_trans_eq, refl }  
                                                     -- preserves compositions of morphisms 
end 

/- The forgetful functor is faithful. -/
@[hott]
def forget_is_faithful {C : Type u} [category.{v} C] (std_str : std_structure_on C) : 
  is_faithful_functor _ _ (forget_str std_str) :=
begin 
  intros str₁ str₂ f₁ f₂ p, fapply sigma.sigma_eq, 
  { apply eq_of_homotopy, intro s, exact apd10 (ap nat_trans.app p) s },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end  

/- We want to construct limits of diagrams of standard structures fom the limits of the associated 
   diagrams in the underlying ategory indexed by the sorts. In principle these diagrams can be 
   retrieved from the forgetful functor, but it is more effective to construct them directly: 
   A `J`-diagram of standard structures yields a tupel of `J`-diagrams in the underlying category, 
   indexed by the sorts. -/
@[hott]
def forget_diagram {J : Type.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  {std_str : std_structure_on C} (F : J ⥤ std_structure std_str) : Π x : std_str.S, J ⥤ C :=
begin
  intro x,
  fapply functor.mk, 
  { intro j, exact (F.obj j).carrier x },
  { intros j k f, exact (F.map f).1 x },
  { intro j, change (F.map (𝟙 j)).1 x = 𝟙 ((F.obj j).carrier x), rwr functor.map_id },
  { intros j k l f g, change (F.map (f ≫ g)).1 x  = ((F.map f).1 x) ≫ ((F.map g).1 x), 
    rwr functor.map_comp }
end  

/- Next, we extract cones in the underlying category indexed by the sorts from a cone of standard structures. -/
@[hott, reducible]
def str_cone_to_sort_cones {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  {std_str : std_structure_on C} {F : J ⥤ (std_structure std_str)} (s : cone F) : 
  Π x : std_str.S, cone (forget_diagram F x) :=
begin 
  intro x, fapply cone.mk, 
  { exact s.X.carrier x },  -- vertex
  { fapply nat_trans.mk,
    { intro j, exact (s.π.app j).1 x },  --transformation of objects
    { intros j k f, hsimp, change (s.π.app k).1 x = (λ x, (s.π.app j).1 x ≫ (F.map f).1 x) x, 
      rwr <- apd10 (comp_hom_std_C _ _) x, rwr <- ap sigma.fst (s.π.naturality f), 
      rwr precategory.id_comp } }  --naturality
end 

/- We can construct the limit cone of a diagram of standard structures from the limit cones of the diagrams of the
   underlying category associated to the sorts if (and only if, but we won' proof that)
   - the tupel of vertices of the limit cones carries a structure,
   - the tupel of leg morphisms of the limit cones associated to each diagram arrow respects the structures,
   - the tupel of lifting morphisms from the vertices of cones associated to each sort to the vertices of the limit 
     cones respect the structures. 
   
   To show this we collect the data of this criterion in a type: -/
@[hott]
structure limit_cone_str_data {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [category.{v} C] {std_str : std_structure_on C} {F : J ⥤ (std_structure std_str)} 
  (lc : Π x : std_str.S, limit_cone (forget_diagram F x)) :=
(lc_str : std_str.P (λ x, (lc x).cone.X)) 
(lc_legs_H : Π (j : J), std_str.H lc_str ((F.obj j).str) (λ x, (lc x).cone.π.app j))
(lift_H : Π (s : cone F), std_str.H s.X.str lc_str (λ x, (lc x).is_limit.lift (str_cone_to_sort_cones s x)))

@[hott]
def str_limit_cone {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  {std_str : std_structure_on C} {F : J ⥤ (std_structure.{v u w} std_str)} 
  (lc : Π x : std_str.S, limit_cone (forget_diagram F x)) (lcd : limit_cone_str_data lc) : limit_cone F :=
begin 
  fapply limit_cone.mk, 
  { fapply cone.mk, -- the limit cone 
    { exact std_structure.mk (λ x, (lc x).cone.X) lcd.lc_str },
    { fapply nat_trans.mk, 
      { intro j, 
        exact ⟨λ x, (lc x).cone.π.app j, lcd.lc_legs_H j⟩ },
      { intros j k f, hsimp, 
        apply @hom_eq_C_std _ _ _ (std_structure.mk (λ x, (lc x).cone.X) lcd.lc_str) (F.obj k), 
        rwr comp_hom_std_C, hsimp, apply eq_of_homotopy, intro x, hsimp, 
        have H : (lc x).cone.π.app k = (𝟙 (lc x).cone.X) ≫ (lc x).cone.π.app k, by rwr precategory.id_comp,
        rwr H, exact (lc x).cone.π.naturality f } } },
  { fapply is_limit.mk, -- the limit cone is a limit
    { intro s, 
      exact ⟨λ x, (lc x).is_limit.lift (str_cone_to_sort_cones s x), lcd.lift_H s⟩ },
    { intros s j, apply hom_eq_C_std, rwr comp_hom_std_C, hsimp, apply eq_of_homotopy, intro x,
      change (lc x).is_limit.lift (str_cone_to_sort_cones s x) ≫ (lc x).cone.π.app j = (s.π.app j).fst x,
      exact (lc x).is_limit.fac (str_cone_to_sort_cones s x) j },
    { intros s m fac_m, apply hom_eq_C_std, hsimp, apply eq_of_homotopy, intro x, 
      have fac_m1 : ∀ j : J, m.1 x ≫ (lc x).cone.π.app j = (str_cone_to_sort_cones s x).π.app j, from 
        begin intro j, change _ = (s.π.app j).1 x, rwr <- apd10 (ap sigma.fst (fac_m j)) x end,
      exact (lc x).is_limit.uniq (str_cone_to_sort_cones s x) (m.1 x) fac_m1 } }
end                

@[hott]
def str_has_limit {J : Set.{u'}} [precategory.{v'} J] {C : Type u} [category.{v} C] 
  [has_limits_of_shape J C] {std_str : std_structure_on C} (F : J ⥤ (std_structure std_str)) 
  (lcd : limit_cone_str_data (λ x, get_limit_cone (forget_diagram F x))) : has_limit F :=
has_limit.mk (str_limit_cone (λ x, get_limit_cone (forget_diagram F x)) lcd)                                           

@[hott, instance]
def std_structure_has_limits_of_shape {J : Set.{u'}} [precategory.{v'} J] {C : Type u} 
  [category.{v} C] [has_limits_of_shape J C] {std_str : std_structure_on C} 
  (lcd_F : Π F : J ⥤ (std_structure std_str), limit_cone_str_data 
                                                (λ x, get_limit_cone (forget_diagram  F x))) : 
  has_limits_of_shape J (std_structure std_str) :=
has_limits_of_shape.mk (λ F, str_has_limit F (lcd_F F))


open signature

/- We define structures of a given signature over a category `C` with products. -/
@[hott]  
structure Sig_structure_on {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] (car : sign.sorts -> C) :=  
( ops : ∀ o : sign.ops, ∏ (λ a : sign.ops_arity o, car (sign.ops_source o a)) ⟶ 
                                                                        car (sign.ops_target o) )
( rels : ∀ r : sign.rels, subobject (∏ (λ a : sign.rels_arity r, car (sign.rels_comp a))) )

@[hott]
def Sig_str_eq {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] {car : sign.sorts -> C} {S T : Sig_structure_on car} :
  (S.ops = T.ops) -> (S.rels = T.rels) -> S = T :=
begin 
  hinduction S with ops₁ rels₁, hinduction T with ops₂ rels₂, hsimp, 
  intros ops_eq rels_eq, exact ap011 Sig_structure_on.mk ops_eq rels_eq 
end

@[hott]
def Sig_str_eq_eta {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] {car : sign.sorts -> C} {S T : Sig_structure_on car} (p : S = T) :
  Sig_str_eq (ap Sig_structure_on.ops p) (ap Sig_structure_on.rels p) = p :=
begin hinduction p, hinduction S, refl end  

@[hott, instance]
def is_set_Sig_str_on {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] (car : sign.sorts -> C) : is_set (Sig_structure_on car) :=
begin
  fapply is_set.mk, intros x y p q, 
  rwr <- Sig_str_eq_eta p, rwr <- Sig_str_eq_eta q,
  apply ap011 Sig_str_eq, apply is_set.elim, apply is_set.elim
end   

@[hott]
structure is_Sig_structure_hom {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] {car₁ car₂ : sign.sorts -> C} (S₁ : Sig_structure_on car₁)
  (S₂ : Sig_structure_on car₂) (f : Π x : sign.sorts, car₁ x ⟶ car₂ x) := 
( ops_pres : Π o : sign.ops, S₁.ops o ≫ f (sign.ops_target o) = 
                                               (∏h (λ a, f (sign.ops_source o a))) ≫ S₂.ops o )
( rels_pres : Π r : sign.rels, Σ h : (S₁.rels r).obj ⟶ (S₂.rels r).obj, 
    (S₁.rels r).hom ≫ (∏h (λ a, f (sign.rels_comp a))) = h ≫ (S₂.rels r).hom )

@[hott, instance]
def is_prop_is_Sig_structure_hom {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] {car₁ car₂ : sign.sorts -> C} {S₁ : Sig_structure_on car₁}
  {S₂ : Sig_structure_on car₂} (f : Π x : sign.sorts, car₁ x ⟶ car₂ x) : 
  is_prop (is_Sig_structure_hom S₁ S₂ f) :=
begin
  fapply is_prop.mk, intros h₁ h₂, hinduction h₁ with op₁ rp₁, hinduction h₂ with op₂ rp₂,
  fapply ap011 is_Sig_structure_hom.mk, 
  { apply eq_of_homotopy, intro o, exact is_prop.elim _ _ },
  { apply eq_of_homotopy, intro r, fapply sigma.sigma_eq, 
    { exact (S₂.rels r).is_mono _ (rp₁ r).1 (rp₂ r).1 ((rp₁ r).2⁻¹⬝(rp₂ r).2) },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end                                                         

@[hott]
def id_is_Sig_str_hom {sign : fo_signature} {C : Type u} [category.{v} C] 
  [has_products.{v u 0} C] {car : sign.sorts -> C} (S : Sig_structure_on car) :
  is_Sig_structure_hom S S (λ x, 𝟙 (car x)) :=
begin 
  fapply is_Sig_structure_hom.mk, 
  { intro o, rwr pi_hom_id, hsimp }, 
  { intro r, fapply dpair, exact 𝟙 (S.rels r).obj, rwr pi_hom_id, hsimp } 
end  

@[hott]
def std_str_of_Sig_str (sign : fo_signature) (C : Type u) [category.{v} C] 
  [has_products.{v u 0} C] : std_structure_on C :=
begin
  fapply std_structure_on.mk,
  { exact sign.sorts }, --sorts
  { exact λ car : sign.sorts -> C, Sig_structure_on car }, --structure
  { intros x y S T h, 
    exact prop_resize (to_Prop (is_Sig_structure_hom S T h)) }, --homomorphisms
  { intros car S, apply prop_to_prop_resize, fapply is_Sig_structure_hom.mk, 
    { intro o, hsimp, rwr pi_hom_id, hsimp },
    { intro r, rwr pi_hom_id, fapply dpair, exact 𝟙 (S.rels r).obj, hsimp } }, --identity
  { intros car₁ car₂ car₃ S T U f g is_hom_f is_hom_g, apply prop_to_prop_resize, 
    fapply is_Sig_structure_hom.mk, 
    { intro o, rwr <- precategory.assoc, 
      rwr (prop_resize_to_prop is_hom_f).ops_pres o, rwr precategory.assoc,
      rwr (prop_resize_to_prop is_hom_g).ops_pres o, rwr <- precategory.assoc,
      rwr pi_hom_comp },
    { intros r, 
      let h₁ := ((prop_resize_to_prop is_hom_f).rels_pres r).1,
      let p₁ := ((prop_resize_to_prop is_hom_f).rels_pres r).2,
      let h₂ := ((prop_resize_to_prop is_hom_g).rels_pres r).1,
      let p₂ := ((prop_resize_to_prop is_hom_g).rels_pres r).2,
      fapply dpair,
      { exact h₁ ≫ h₂ },
      { rwr <- pi_hom_comp, rwr <- precategory.assoc, rwr p₁, rwr precategory.assoc, rwr p₂, 
        rwr <- precategory.assoc } } }, --composition
  { intros car S T, fapply equiv.mk, 
    { intro Sig_homs, 
      hinduction S with ops₁ rels₁, hinduction T with ops₂ rels₂, 
      fapply ap011 Sig_structure_on.mk, 
      { apply eq_of_homotopy, intro o, 
        rwr <- precategory.id_comp (ops₂ o), rwr <- precategory.comp_id (ops₁ o),
        rwr <- pi_hom_id, exact (prop_resize_to_prop Sig_homs.1).ops_pres o },
      { apply eq_of_homotopy, intro r, apply (iso_mono_to_equal_subobj _ _),
        apply (homs_eqv_iso_of_monos _ _).to_fun, fapply pair,
        { fapply hom_of_monos.mk, 
          { exact ((prop_resize_to_prop Sig_homs.1).rels_pres r).1 }, 
          { let p₁ := ((prop_resize_to_prop Sig_homs.1).rels_pres r).2, rwr <- p₁, rwr pi_hom_id,
            hsimp } }, 
        { fapply hom_of_monos.mk, 
          { exact ((prop_resize_to_prop Sig_homs.2).rels_pres r).1 }, 
          { let p₂ := ((prop_resize_to_prop Sig_homs.2).rels_pres r).2, rwr <- p₂, rwr pi_hom_id,
            hsimp } } } },
    { fapply adjointify, 
      { intro Sig_str_eq, rwr Sig_str_eq, apply pair,
        exact prop_to_prop_resize (id_is_Sig_str_hom T), 
        exact prop_to_prop_resize (id_is_Sig_str_hom T) },
      { intro b, exact is_set.elim _ _ },
      { intro a, exact is_prop.elim _ _ } } } --standard structure
end  

@[hott, reducible]
def Sig_structure (sign : fo_signature) (C : Type u) [category.{v} C] [has_products.{v u 0} C] :=
  std_structure (std_str_of_Sig_str sign C)

@[hott, instance]
def Sig_str_precategory (sign : fo_signature) (C : Type u) [category.{v} C] [has_products.{v u 0} C] : 
  precategory (Sig_structure sign C) := 
std_str_precategory (std_str_of_Sig_str sign C)

@[hott, instance]
def Sig_str_category (sign : fo_signature) (C : Type u) [category.{v} C] [has_products.{v u 0} C] : 
  category (Sig_structure sign C) := 
structure_identity_principle (std_str_of_Sig_str sign C)


end categories

end hott