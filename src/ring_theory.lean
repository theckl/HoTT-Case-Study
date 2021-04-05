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

/- Showing the HoTTism that all the ring homomrphisms between two
   commuative rings form a set requires many lines of code. The proofs
   are straightforward and seem automatizable, but the construction of 
   the types is elaborate. -/
@[hott]
def ring_hom_eta {M N : CommRing} (f : M →+* N) : 
  f = ring_hom.mk f.to_fun f.map_one f.map_mul f.map_zero f.map_add :=
begin hinduction f, refl end

@[hott]
def rh_fun_eq {M N : CommRing} {f g : M →+* N} (p : f = g) : 
  f.to_fun = g.to_fun :=
ap ring_hom.to_fun p 

@[hott]
def rh_map_one_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_one =[rh_fun_eq p; λ h : M -> N, h 1 = 1] g.map_one :=
pathover_ap (λ h : M -> N, h 1 = 1) ring_hom.to_fun 
                               (@apd (M →+* N) _ _ _ ring_hom.map_one p)  

@[hott]
def rh_map_mul_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_mul =[rh_fun_eq p; 
              λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b] g.map_mul :=
pathover_ap (λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b) 
                   ring_hom.to_fun (@apd (M →+* N) _ _ _ ring_hom.map_mul p)              

@[hott]
def rh_map_zero_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_zero =[rh_fun_eq p; λ h : M -> N, h 0 = 0] g.map_zero :=
pathover_ap (λ h : M -> N, h 0 = 0) ring_hom.to_fun 
                               (@apd (M →+* N) _ _ _ ring_hom.map_zero p)  

@[hott]
def rh_map_add_eq {M N : CommRing} {f g : M →+* N} (p : f = g) :
  f.map_add =[rh_fun_eq p; 
              λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b] g.map_add :=
pathover_ap (λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b) 
                   ring_hom.to_fun (@apd (M →+* N) _ _ _ ring_hom.map_add p)              

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
      @is_set.elim (M -> N) (@set.is_set_map _ _) _ _ (rh_fun_eq p) (rh_fun_eq q),
    have one_eq_eq : rh_map_one_eq p =[fun_eq_eq; 
      λ r : g.to_fun = h.to_fun, g.map_one =[r; λ f : M -> N, f 1 = 1] h.map_one] 
                     rh_map_one_eq q, from sorry,
    have mul_eq_eq : rh_map_mul_eq p =[fun_eq_eq;
      λ r : g.to_fun = h.to_fun, g.map_mul =[r; 
                       λ f : M -> N, ∀ a b : M, f (a * b) = f a * f b] h.map_mul] 
                     rh_map_mul_eq q, from sorry,  
    have zero_eq_eq : rh_map_zero_eq p =[fun_eq_eq; 
      λ r : g.to_fun = h.to_fun, g.map_zero =[r; λ f : M -> N, f 0 = 0] h.map_zero] 
                     rh_map_zero_eq q, from sorry,
    have add_eq_eq : rh_map_add_eq p =[fun_eq_eq;
      λ r : g.to_fun = h.to_fun, g.map_add =[r; 
                       λ f : M -> N, ∀ a b : M, f (a + b) = f a + f b] h.map_add] 
                     rh_map_add_eq q, from sorry,                  
    begin 
      rwr ring_hom_eq_eta p, rwr ring_hom_eq_eta q,
      apply whisker_right (ring_hom_eta h)⁻¹, apply whisker_left (ring_hom_eta g),
      exact apd01111_eq ring_hom.mk fun_eq_eq one_eq_eq mul_eq_eq 
                                    zero_eq_eq add_eq_eq 
    end, 
  is_set.mk _ set_eq_eq 

end algebra

end hott
