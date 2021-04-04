import hott.algebra.ring categorial_limits pathover2

universes u v w
hott_theory

namespace hott
open is_trunc hott.algebra category_theory 

namespace algebra

/- Bundled structure of commutative rings -/
@[hott] 
structure CommRing :=
(carrier : Type u) (struct : comm_ring carrier)

@[hott]
instance has_coe_CommRing : has_coe_to_sort CommRing.{u} :=
  ⟨Type u, CommRing.carrier⟩

attribute [instance] CommRing.struct

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
def ring_hom_eq_eta {M N : CommRing} {f g : M →+* N} (p : f = g) :
  let p_fun := ap ring_hom.to_fun p, 
      p_map_one := pathover_ap (λ h : M -> N, h 1 = 1) ring_hom.to_fun 
                               (@apd (M →+* N) _ _ _ ring_hom.map_one p),
      p_map_mul := pathover_ap (λ h : M -> N, ∀ a b : M, h (a * b) = h a * h b) 
                   ring_hom.to_fun (@apd (M →+* N) _ _ _ ring_hom.map_mul p),
      p_map_zero := pathover_ap (λ h : M -> N, h 0 = 0) ring_hom.to_fun 
                                (@apd (M →+* N) _ _ _ ring_hom.map_zero p),
      p_map_add := pathover_ap (λ h : M -> N, ∀ a b : M, h (a + b) = h a + h b) 
                   ring_hom.to_fun (@apd (M →+* N) _ _ _ ring_hom.map_add p) in
  p = (ring_hom_eta f) ⬝ 
      (apd01111 ring_hom.mk (rh_fun_eq p) (rh_map_one_eq p) p_map_mul p_map_zero p_map_add) ⬝ 
      (ring_hom_eta g)⁻¹ :=
begin hinduction p, hinduction f, hsimp end 

@[hott, instance]
def ring_hom_is_set (M N : CommRing) : is_set (M →+* N) :=
  have set_eq_eq : ∀ (g h : M →+* N) (p q : g = h), p = q, from
    begin intros g h p q, rwr ring_hom_eq_eta p, sorry end, 
  is_set.mk _ set_eq_eq 

end algebra

end hott
