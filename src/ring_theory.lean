import hott.algebra.ring set_theory categorial_limits pathover2

universes u v w
hott_theory

namespace hott
open is_trunc hott.is_equiv hott.algebra hott.set category_theory 

namespace algebra

/- Bundled structure of commutative rings -/
@[hott] 
structure CommRing :=
(carrier : Set) (struct : comm_ring carrier)

@[hott]
instance CommRing_to_Set : has_coe CommRing.{u} Set.{u} :=
  ⟨CommRing.carrier⟩

@[hott]
instance CommRing_to_Type : has_coe_to_sort CommRing.{u} :=
  has_coe_to_sort.mk (Type u) (λ R : CommRing, ↥R.carrier)  

attribute [instance] CommRing.struct

/- We now construct the category structure on commutative rings. 

   We first define ring homomorphisms without inheritance, as for 
   this project, we do not need homomorphisms of monoids and groups. -/
@[hott]
structure ring_hom (M N : CommRing.{u}) :=
  (to_fun : M -> N)
  (map_one : to_fun 1 = 1)
  (map_mul : ∀ a b : M, to_fun (a * b) = to_fun a * to_fun b)
  (map_zero : to_fun 0 = 0)
  (map_add : ∀ a b : M, to_fun (a + b) = to_fun a + to_fun b)

infixr ` →+* `:25 := ring_hom

@[hott]
instance ring_hom_to_fun (M N : CommRing) : 
  has_coe_to_fun (ring_hom M N) :=
⟨λ _, M -> N, λ h, h.to_fun⟩  

/- Needed for calculations. -/
@[hott]
def rh_map_one {R S : CommRing} (f : R →+* S) :
  f 1 = 1 :=
f.map_one   

@[hott]
def rh_map_mul {R S : CommRing} (f : R →+* S) :
  ∀ r₁ r₂ : R, f (r₁ * r₂) = f r₁ * f r₂ :=
f.map_mul  

@[hott]
def rh_map_zero {R S : CommRing} (f : R →+* S) :
  f 0 = 0 :=
f.map_zero   

@[hott]
def rh_map_add {R S : CommRing} (f : R →+* S) :
  ∀ r₁ r₂ : R, f (r₁ + r₂) = f r₁ + f r₂ :=
f.map_add

/- We show the HoTTism that all the ring homomrphisms between two
   commutative rings by showing that ring homomorphisms are completely
   determined by the map between the underlying sets. This means that the
   forgetful functor from rings to sets is faithful. 
   
   Most of the proofs use that the structure equations are propositions
   because the source and target of the homomorphisms are sets. -/
@[hott]
def ring_hom_eta {M N : CommRing} (f : M →+* N) : 
  f = ring_hom.mk f.to_fun f.map_one f.map_mul f.map_zero f.map_add :=
begin hinduction f, refl end

@[hott, hsimp]
def rh_fun_eq {M N : CommRing} {f g : M →+* N} (p : f = g) : 
  f.to_fun = g.to_fun :=
ap ring_hom.to_fun p 

@[hott, hsimp, reducible]
def rh_fun_one_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_one =[p; λ h : M -> N, h 1 = 1] g.map_one :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end  

@[hott, hsimp]
def rh_fun_mul_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_mul 
    =[p; λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b] g.map_mul :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end    

@[hott, hsimp]
def rh_fun_zero_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_zero =[p; λ h : M -> N, h 0 = 0] g.map_zero :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end  

@[hott, hsimp]
def rh_fun_add_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_add 
    =[p; λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b] g.map_add :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end

@[hott, hsimp]
def rh_fun_to_hom {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) : f = g :=
  (ring_hom_eta f) ⬝ 
  (apd01111 ring_hom.mk p (rh_fun_one_eq p) (rh_fun_mul_eq p) 
                          (rh_fun_zero_eq p) (rh_fun_add_eq p)) ⬝ 
  (ring_hom_eta g)⁻¹

/- I don't understand why this proof must be so long. I was not able to tell
   Lean how to process the `idp` and `refl` arguments automatically. -/
@[hott]
def rh_fun_hom_rinv {M N : CommRing} {f g : M →+* N} (p : f = g) :
  rh_fun_to_hom (rh_fun_eq p) = p :=
have r₁ : rh_fun_one_eq (refl ⇑f) = idpo, by hsimp; refl, 
have r₂ : rh_fun_mul_eq (refl ⇑f) = idpo, by hsimp; refl,
have r₃ : rh_fun_zero_eq (refl ⇑f) = idpo, by hsimp; refl, 
have r₄ : rh_fun_add_eq (refl ⇑f) = idpo, by hsimp; refl,
have q : apd01111 ring_hom.mk (refl ⇑f) (rh_fun_one_eq (refl ⇑f)) 
         (rh_fun_mul_eq (refl ⇑f)) (rh_fun_zero_eq (refl ⇑f))
         (rh_fun_add_eq (refl ⇑f)) = idp, 
  by rwr r₁; rwr r₂; rwr r₃; rwr r₄; hsimp,   
begin 
  hinduction p, change rh_fun_to_hom (refl f) = refl f,
  change (ring_hom_eta f) ⬝ _ ⬝ (ring_hom_eta f)⁻¹ = idp,
  rwr q, rwr con_idp, rwr con.right_inv 
end

@[hott]
def rh_fun_hom_linv {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  rh_fun_eq (rh_fun_to_hom p) = p :=
@is_set.elim (M -> N) _ _ _ _ _  

@[hott]
def rh_fun_eq_equiv_hom_eq {M N : CommRing} (f g : M →+* N) : 
  (⇑f = g) ≃ (f = g) :=
equiv.mk rh_fun_to_hom (adjointify rh_fun_to_hom rh_fun_eq 
                                   rh_fun_hom_rinv rh_fun_hom_linv)   

@[hott, instance]
def ring_hom_is_set (M N : CommRing) : is_set (M →+* N) :=
  have set_eq_eq : ∀ (g h : M →+* N) (p q : g = h), p = q, from
    assume g h,
    have is_prop_fun_eq : is_prop (⇑g = h), from 
      is_prop.mk (@is_set.elim (M -> N) _ _ _),
    have is_prop_hom_eq : is_prop (g = h), from 
      is_trunc_equiv_closed -1 (rh_fun_eq_equiv_hom_eq g h) is_prop_fun_eq,
    @is_prop.elim _ is_prop_hom_eq, 
  is_set.mk _ set_eq_eq   

/- Next, we define the category structure on `CommRing`. -/
@[hott, instance]
def ring_has_hom : has_hom CommRing :=
  has_hom.mk (λ R S : CommRing, Set.mk (ring_hom R S) (ring_hom_is_set R S))

@[hott, hsimp, reducible]
def id_CommRing (R : CommRing) : R ⟶ R :=
  let id_R := @set.id R in
  have one_R : id_R 1 = 1, by refl,
  have mul_R : ∀ r s : R, id_R (r * s) = (id_R r) * (id_R s), 
    by intros r s; refl,
  have zero_R : id_R 0 = 0, by refl,
  have add_R : ∀ r s : R, id_R (r + s) = (id_R r) + (id_R s), 
    by intros r s; refl,
  ring_hom.mk id_R one_R mul_R zero_R add_R

@[hott, hsimp, reducible]
def comp_CommRing {R S T : CommRing} (f : R →+* S) (g : S →+* T) : R →+* T :=
  let h := λ r : R, g (f r) in
  have h_one : h 1 = 1, from
    calc h 1 = g (f 1) : rfl
         ... = g 1 : by rwr rh_map_one
         ... = 1 : by rwr rh_map_one,
  have h_mul : ∀ r₁ r₂ : R, h (r₁ * r₂) = h r₁ * h r₂, from assume r₁ r₂, 
    calc h (r₁ * r₂) = g (f (r₁ * r₂)) : rfl
         ... = g (f r₁ * f r₂) : by rwr rh_map_mul
         ... = g (f r₁) * g (f r₂) : by rwr rh_map_mul
         ... = h r₁ * h r₂ : rfl,
  have h_zero : h 0 = 0, from 
    calc h 0 = g (f 0) : rfl
         ... = g 0 : by rwr rh_map_zero
         ... = 0 : by rwr rh_map_zero,
  have h_add : ∀ r₁ r₂ : R, h (r₁ + r₂) = h r₁ + h r₂, from assume r₁ r₂, 
    calc h (r₁ + r₂) = g (f (r₁ + r₂)) : rfl
         ... = g (f r₁ + f r₂) : by rwr rh_map_add
         ... = g (f r₁) + g (f r₂) : by rwr rh_map_add
         ... = h r₁ + h r₂ : rfl,
  ring_hom.mk h h_one h_mul h_zero h_add

@[hott, instance]
def CommRing_cat_struct : category_struct CommRing :=
  category_struct.mk id_CommRing @comp_CommRing

/- The equalities of homomorphisms making up a precategory follow from 
   the equalities of the maps on the underlying sets. -/
@[hott, hsimp]
def id_comp_CommRing {R S : CommRing.{u}} : Π (f : R ⟶ S), 
  𝟙 R ≫ f = f :=
assume f,  
have hom_eq : ∀ r : R, (𝟙 R ≫ f) r = f r, from assume r, rfl,
have fun_eq : ⇑(𝟙 R ≫ f) = f, from eq_of_homotopy hom_eq,   
rh_fun_to_hom fun_eq  

@[hott, hsimp]
def comp_id_CommRing {R S : CommRing.{u}} : Π (f : R ⟶ S), 
  f ≫ 𝟙 S = f :=
assume f,  
have hom_eq : ∀ r : R, (f ≫ 𝟙 S) r = f r, from assume r, rfl,
have fun_eq : ⇑(f ≫ 𝟙 S) = f, from eq_of_homotopy hom_eq,   
rh_fun_to_hom fun_eq

@[hott, hsimp]
def assoc_CommRing {R S T U : CommRing.{u}} : 
  Π (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U), (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
assume f g h,
have hom_eq : ∀ r : R, ((f ≫ g) ≫ h) r = (f ≫ (g ≫ h)) r, from assume r, rfl,
have fun_eq : ⇑((f ≫ g) ≫ h) = f ≫ (g ≫ h), from eq_of_homotopy hom_eq, 
rh_fun_to_hom fun_eq 

@[hott, instance]
def CommRing_precategory : precategory CommRing.{u} :=
  precategory.mk @id_comp_CommRing @comp_id_CommRing @assoc_CommRing

/- We now show that `CommRing` is a category. 

   To this purpose we use univalence to construct an equality of rings
  from an isomorphy. This is noncomputable. -/
@[hott]
def CommRing_isotoSetid (R S : CommRing) : R ≅ S -> R.carrier = S.carrier :=
  assume isoRS,
  let h := ⇑isoRS.hom, i := ⇑isoRS.inv in
  have r_inv : ∀ s : S, h (i s) = s, from assume s, 
    calc h (i s) = (isoRS.inv ≫ isoRS.hom) s : by refl 
         ... = (id_CommRing S) s : by rwr isoRS.r_inv
         ... = s : by refl,
  have l_inv : ∀ r : R, i (h r) = r, from assume r, 
    calc i (h r) = (isoRS.hom ≫ isoRS.inv) r : by refl 
         ... = (id_CommRing R) r : by rwr isoRS.l_inv
         ... = r : by refl, 
  have equivRS : R ≃ S, from equiv.mk h (adjointify h i r_inv l_inv),             
  have eqTypeRS : ↥R = ↥S, from ua equivRS, 
  set_eq_equiv_car_eq.symm.to_fun eqTypeRS

#check comm_ring.mk

end algebra

end hott
