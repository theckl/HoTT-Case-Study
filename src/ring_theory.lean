import hott.algebra.ring set_theory categorial_limits pathover2

universes u v w
hott_theory

namespace hott
open is_trunc hott.algebra set category_theory 

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

/- Showing the HoTTism that all the ring homomrphisms between two
   commutative rings form a set requires many lines of code. The proofs
   are straightforward and seem automatizable, but the construction of 
   the types is elaborate. -/
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

@[hott]
def rh_map_one_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_one =[rh_fun_eq p; λ h : M -> N, h 1 = 1] g.map_one :=
pathover_ap (λ h : M -> N, h 1 = 1) ring_hom.to_fun 
                               (@apd (M →+* N) _ _ _ ring_hom.map_one p)  

@[hott, hsimp]
def rh_fun_mul_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_mul 
    =[p; λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b] g.map_mul :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end    

@[hott]
def rh_map_mul_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_mul =[rh_fun_eq p; 
              λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b] g.map_mul :=
pathover_ap (λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b) 
                   ring_hom.to_fun (@apd (M →+* N) _ _ _ ring_hom.map_mul p)              

@[hott, hsimp]
def rh_fun_zero_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_zero =[p; λ h : M -> N, h 0 = 0] g.map_zero :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end  

@[hott]
def rh_map_zero_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_zero =[rh_fun_eq p; λ h : M -> N, h 0 = 0] g.map_zero :=
pathover_ap (λ h : M -> N, h 0 = 0) ring_hom.to_fun 
                               (@apd (M →+* N) _ _ _ ring_hom.map_zero p)  

@[hott, hsimp]
def rh_fun_add_eq {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  f.map_add 
    =[p; λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b] g.map_add :=
begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end

@[hott]
def rh_map_add_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_add =[rh_fun_eq p; 
              λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b] g.map_add :=
pathover_ap (λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b) 
                   ring_hom.to_fun (@apd (M →+* N) _ _ _ ring_hom.map_add p)              

@[hott, hsimp]
def rh_fun_to_hom {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) : f = g :=
  (ring_hom_eta f) ⬝ 
  (apd01111 ring_hom.mk p (rh_fun_one_eq p) (rh_fun_mul_eq p) 
                          (rh_fun_zero_eq p) (rh_fun_add_eq p)) ⬝ 
  (ring_hom_eta g)⁻¹

@[hott]
def rh_fun_hom_rinv {M N : CommRing} {f g : M →+* N} (p : f = g) :
  rh_fun_to_hom (rh_fun_eq p) = p :=
have r : rh_fun_one_eq (refl ⇑f) = idpo, by hsimp; refl,  
have q : apd01111 ring_hom.mk (refl ⇑f) (rh_fun_one_eq (refl ⇑f)) 
         (rh_fun_mul_eq (refl ⇑f)) (rh_fun_zero_eq (refl ⇑f))
         (rh_fun_add_eq (refl ⇑f)) = rfl, from sorry,   
begin hinduction p, change rh_fun_to_hom (refl f) = refl f,
      change (ring_hom_eta f) ⬝ _ ⬝ (ring_hom_eta f)⁻¹ = refl f,
      rwr q,
      sorry end

@[hott]
def rh_fun_hom_linv {M N : CommRing} {f g : M →+* N} (p : ⇑f = g) :
  rh_fun_eq (rh_fun_to_hom p) = p :=
sorry  

@[hott]
def ring_hom_eq_eta {M N : CommRing} {f g : M →+* N} (p : f = g) :
  p = (ring_hom_eta f) ⬝ 
      (apd01111 ring_hom.mk (rh_fun_eq p) (rh_map_one_eq p) (rh_map_mul_eq p) 
                            (rh_map_zero_eq p) (rh_map_add_eq p)) ⬝ 
      (ring_hom_eta g)⁻¹ :=
begin hinduction p, hinduction f, hsimp end 

@[hott, instance]
def ring_hom_is_set (M N : CommRing) : is_set (M →+* N) :=
  have set_eq_eq : ∀ (g h : M →+* N) (p q : g = h), p = q, from
    assume g h p q,
    have fun_eq_eq : rh_fun_eq p = rh_fun_eq q, from 
      @is_set.elim (M -> N) _ _ _ (rh_fun_eq p) (rh_fun_eq q),
    have one_eq_eq : rh_map_one_eq p =[fun_eq_eq; 
      λ r : g.to_fun = h.to_fun, g.map_one =[r; λ f : M -> N, f 1 = 1] h.map_one] 
                     rh_map_one_eq q, from 
      have one_eq_prop : is_prop 
        (g.map_one =[rh_fun_eq q; λ h : M -> N, h 1 = 1] h.map_one), from
        is_trunc_equiv_closed_rev -1 (@pathover_equiv_tr_eq _ (λ h : M -> N, h 1 = 1) 
          _ _ (rh_fun_eq q) g.map_one h.map_one) (is_trunc_eq -1 _ _),               
      begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,
    have mul_eq_eq : rh_map_mul_eq p =[fun_eq_eq;
      λ r : g.to_fun = h.to_fun, g.map_mul =[r; 
                       λ f : M -> N, ∀ a b : M, f (a * b) = f a * f b] h.map_mul] 
                     rh_map_mul_eq q, from 
      have mul_eq_prop : is_prop
        (g.map_mul =[rh_fun_eq q; λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b] 
                                  h.map_mul), from 
        is_trunc_equiv_closed_rev -1 (@pathover_equiv_tr_eq _ (λ h : M -> N, 
          ∀ a b : M, h (a * b) = h a * h b) _ _ (rh_fun_eq q) g.map_mul h.map_mul) 
          (is_trunc_eq -1 _ _),               
      begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,  
    have zero_eq_eq : rh_map_zero_eq p =[fun_eq_eq; 
      λ r : g.to_fun = h.to_fun, g.map_zero =[r; λ f : M -> N, f 0 = 0] h.map_zero] 
                     rh_map_zero_eq q, from 
      have zero_eq_prop : is_prop 
        (g.map_zero =[rh_fun_eq q; λ h : M -> N, h 0 = 0] h.map_zero), from
        is_trunc_equiv_closed_rev -1 (@pathover_equiv_tr_eq _ (λ h : M -> N, h 0 = 0) 
          _ _ (rh_fun_eq q) g.map_zero h.map_zero) (is_trunc_eq -1 _ _),               
      begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,
    have add_eq_eq : rh_map_add_eq p =[fun_eq_eq;
      λ r : g.to_fun = h.to_fun, g.map_add =[r; 
                       λ f : M -> N, ∀ a b : M, f (a + b) = f a + f b] h.map_add] 
                     rh_map_add_eq q, from 
      have add_eq_prop : is_prop
        (g.map_add =[rh_fun_eq q; λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b] 
                                  h.map_add), from 
        is_trunc_equiv_closed_rev -1 (@pathover_equiv_tr_eq _ (λ h : M -> N, 
          ∀ a b : M, h (a + b) = h a + h b) _ _ (rh_fun_eq q) g.map_add h.map_add) 
          (is_trunc_eq -1 _ _), 
      begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,                     
    begin 
      rwr ring_hom_eq_eta p, rwr ring_hom_eq_eta q,
      apply whisker_right (ring_hom_eta h)⁻¹, apply whisker_left (ring_hom_eta g),
      exact apd01111_eq ring_hom.mk fun_eq_eq one_eq_eq mul_eq_eq 
                                    zero_eq_eq add_eq_eq 
    end, 
  is_set.mk _ set_eq_eq 

/- Next, we define the category structure on `CommRing`. -/
@[hott, instance]
def ring_has_hom : has_hom CommRing :=
  has_hom.mk (λ R S : CommRing, Set.mk (ring_hom R S) (ring_hom_is_set R S))

@[hott, hsimp, reducible]
def id_CommRing (R : CommRing) : R →+* R :=
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


@[hott, hsimp]
def id_comp_CommRing {R S : CommRing} : Π (f : R ⟶ S), 
  𝟙 R ≫ f = f :=
sorry  

@[hott, hsimp]
def comp_id_CommRing {R S : CommRing} : Π (f : R ⟶ S), 
  f ≫ 𝟙 S = f :=
sorry 

@[hott, hsimp]
def assoc_CommRing {R S T U : CommRing} : 
  Π (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U), (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
sorry 

@[hott, instance]
def CommRing_precategory : precategory CommRing :=
  precategory.mk @id_comp_CommRing @comp_id_CommRing @assoc_CommRing

end algebra

end hott
