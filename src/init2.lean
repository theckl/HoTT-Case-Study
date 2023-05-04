import hott.init hott.types.trunc

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc hott.is_equiv

set_option pp.universes false

/- Should be in [init.function]. -/
@[inline, reducible] def function.comp {α β φ : Type _} (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

hott_theory_cmd "local infixr  ` ∘ `:80      := hott.function.comp"

/- Should be in [init.path]. -/
notation eq `▸[`:50 P:0 `]`:0 b:50 := transport P eq b 

@[hott, hsimp, reducible]
def id {A : Type _} (a : A) : A := a 

/- All these equalities of pathovers, concatenations and transports of 
   identities should be produced by tactics. -/
@[hott]
def id_tr_eq_id_inv_con {A : Type _} {a₀ a₁ a₂ : A} (q : a₁ = a₂) (p : a₁ = a₀) :
  q ▸ p = q⁻¹ ⬝ p :=
begin hinduction q, rwr idp_tr, rwr idp_inv, rwr idp_con end  

@[hott]
def pathover_idp_of_id {A : Type _} : Π a : A, pathover_idp_of_eq id (@idp _ a) = idpo := 
  assume a, rfl

@[hott, hsimp]
def pathover_idp_of_eq_eq_of_pathover_idp {A : Type _} {B : A -> Type _} {a : A} 
  {b b': B a} (p : b =[idpath a] b') : pathover_idp_of_eq B (eq_of_pathover_idp p) = p :=
by hinduction p; refl

@[hott]
def po_eq_eq_con {A : Type _} {a b c : A} (p : a = c) (q : b = c)
  (r : a = b) : p =[r; λ d : A, d = c] q -> p = r ⬝ q :=
by hinduction r; intro P; rwr idp_con; rwr eq_of_pathover_idp P

@[hott]
def eq_con_po_eq {A : Type _} {a b c : A} (p : a = c) (q : b = c)
  (r : a = b) : p = r ⬝ q -> p =[r; λ d : A, d = c] q :=
by hinduction r; intro P; rwr idp_con at P; exact pathover_idp_of_eq _ P

@[hott]
def is_contr_tot_peq {A : Type u} (a₀ : A) : 
  is_contr (Σ (a : A), a₀ = a) :=
begin 
  fapply is_contr.mk,
  { exact ⟨a₀, idp⟩ },
  { intro dp, hinduction dp with a p, fapply sigma.sigma_eq,
    exact p, hsimp, apply pathover_of_tr_eq, hsimp }
end


@[hott]
def ap10_eq_of_homotopy {A B : Type _} {f g : A -> B} (Hp : f ~ g) :
  ap10 (eq_of_homotopy Hp) = Hp :=
begin change apd10 _ = _, exact apd10_eq_of_homotopy Hp end

@[reducible,hott]
def ap100 {A B C : Type _} {f g : A → B -> C} (H : f = g) : f ~2 g := apd100 H

@[hott]
def ap100_ev_ap {A B C : Type _} {f g : A → B -> C} (H : f = g) (a : A) (b : B) :
  ap100 H a b = ap (λ h : A -> B -> C, h a b) H :=
by hinduction H; refl

@[reducible,hott]
def ap1000 {A B C D: Type _} {f g : A → B -> C -> D} (H : f = g) : f ~3 g := apd1000 H

@[hott]
def eq_of_homotopy2_inv {A B C : Type _} {f g : A → B -> C} (H : f ~2 g) :
  (eq_of_homotopy2 H)⁻¹ = eq_of_homotopy2 (λ a b, (H a b)⁻¹) :=
begin 
  change (eq_of_homotopy (λ a : A, eq_of_homotopy (λ b : B, H a b)))⁻¹ = 
         (eq_of_homotopy _), 
  rwr <- eq_of_homotopy_inv, apply ap eq_of_homotopy, 
  apply eq_of_homotopy, intro a, hsimp, rwr eq_of_homotopy_inv
end  

@[hott]
def ap100_eq_of_hty2_inv {A B C : Type _} {f g : A → B -> C} (H : f ~2 g) :
  ap100 (eq_of_homotopy2 H) = H :=
is_equiv.left_inv (funext.is_equiv_apd100 f g).inv H 

@[hott]
def apd100_eq_of_hty2_inv {A : Type _} {B : A -> Type _} 
  {C : Π (a : A), B a -> Type _} {f g : Π (a : A) (b : B a), C a b} 
  (H : f ~2 g) (a : A) (b : B a) :
  apd100 (eq_of_homotopy2 H) a b = H a b :=
apd100 (is_equiv.left_inv (funext.is_equiv_apd100 f g).inv H) a b

@[hott]
def ap_ev_eq_of_hty2_ev {A B C : Type _} {f g : A → B -> C} (H : f ~2 g) 
  (a : A) (b : B) :
  ap (λ h : A -> B -> C, h a b) (eq_of_homotopy2 H) = H a b := 
by rwr <- ap100_ev_ap; rwr ap100_eq_of_hty2_inv; refl

@[hott]
def hty2_of_ap100_eq_inv {A B C : Type _} {f g : A → B -> C} (p : f = g) :
  eq_of_homotopy2 (ap100 p) = p :=
is_equiv.right_inv (funext.is_equiv_apd100 f g).inv p 

@[hott]
def ap0111 {A : Type u} {B : Type v} {C D : A -> B -> Type _} {E : Type _}
  (f : Π (a : A) (b : B), C a b -> D a b -> E)
  {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂}
  (p₁ : a₁ = a₂) (p₂ : b₁ = b₂) (p₃ : c₁ =[ap011 C p₁ p₂; id] c₂) 
  (p₄ : d₁ =[ap011 D p₁ p₂; id] d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ := 
begin hinduction p₁, hinduction p₂, hinduction p₃, hinduction p₄, refl end  

@[hott]
def ap0111' {A B C : Type _} {D : Type _} (f : A -> B -> C -> D)
  {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} (p₁ : a₁ = a₂) 
  (p₂ : b₁ = b₂) (p₃ : c₁ = c₂) :
  f a₁ b₁ c₁ = f a₂ b₂ c₂ := 
begin hinduction p₁, hinduction p₂, hinduction p₃, refl end

@[hott] 
def apd0111' {A : Type _} {B C : A -> Type _} {D : Type _} 
  (f : Π (a : A), B a -> C a → D) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} 
  {c₂ : C a₂} (Ha : a₁ = a₂) (Hb : b₁ =[Ha] b₂) (Hc : c₁ =[Ha] c₂) :
  f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
  begin hinduction Hb, hinduction Hc, refl end

@[hott] 
def apd0111'' {A : Type _} {B D : A -> Type _} 
  {C : Π (a : A), B a -> Type _} 
  (f : Π (a : A) (b : B a), C a b → D a) {a₁ a₂ : A} {b₁ : B a₁} 
  {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (Ha : a₁ = a₂) 
  (Hb : b₁ =[Ha] b₂) (Hc : c₁ =[apd011 C Ha Hb; id] c₂) :
  f a₁ b₁ c₁ =[Ha] f a₂ b₂ c₂ :=
  begin hinduction Hb, hinduction Hc, refl end

@[hott]
def apd001 {A B D : Type _} {C : A -> B -> Type _} (f : Π (a : A) (b : B), C a b -> D) 
  {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
  (p₁ : a₁ = a₂) (p₂ : b₁ = b₂) (p₃ : c₁ =[ap011 C p₁ p₂; id] c₂) : 
  f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
begin hinduction p₁, hinduction p₂, hinduction p₃, refl end  

@[hott]
def ap_4 {A B C D E : Type _} (f : A -> B -> C -> D -> E) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
  {d₁ d₂ : D} (pA : a₁ = a₂) (pB : b₁ = b₂) (pC : c₁ = c₂) (pD : d₁ = d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD, refl end  

@[hott, hsimp]
def ap_5 {A B C D E F : Type _} (f : A -> B -> C -> D -> E -> F) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
  {d₁ d₂ : D} {e₁ e₂ : E} (pA : a₁ = a₂) (pB : b₁ = b₂) (pC : c₁ = c₂) (pD : d₁ = d₂) (pE : e₁ = e₂) :
  f a₁ b₁ c₁ d₁ e₁ = f a₂ b₂ c₂ d₂ e₂ :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD, hinduction pE, refl end

@[hott]
def ap_11 {A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ B₀ B₁ C : Type _} 
          (f : A₁ -> A₂ -> A₃ -> A₄ -> A₅ -> A₆ -> A₇ -> A₈ -> A₉ -> B₀ -> B₁ -> C)
          {a₁ a₁' : A₁} {a₂ a₂' : A₂} {a₃ a₃' : A₃} {a₄ a₄' : A₄} {a₅ a₅' : A₅}
          {a₆ a₆' : A₆} {a₇ a₇' : A₇} {a₈ a₈' : A₈} {a₉ a₉' : A₉} {b₀ b₀' : B₀}
          {b₁ b₁' : B₁} (p₁ : a₁ = a₁') (p₂ : a₂ = a₂') (p₃ : a₃ = a₃') 
          (p₄ : a₄ = a₄') (p₅ : a₅ = a₅') (p₆ : a₆ = a₆') (p₇ : a₇ = a₇')
          (p₈ : a₈ = a₈') (p₉ : a₉ = a₉') (q₀ : b₀ = b₀') (q₁ : b₁ = b₁') :
  f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ b₀ b₁ = f a₁' a₂' a₃' a₄' a₅' a₆' a₇' a₈' a₉' b₀' b₁' :=
begin 
  hinduction p₁, hinduction p₂, hinduction p₃, hinduction p₄, hinduction p₅,
  hinduction p₆, hinduction p₇, hinduction p₈, hinduction p₉, hinduction q₀,
  hinduction q₁, refl   
end  

@[hott]
def apo01 {A B : Type _} {C : B -> Type _} (f : A -> B) 
  (g : Π a : A, C (f a)) {a₁ a₂ : A} (p : a₁ = a₂) : 
  g a₁ =[p; λ a : A, C (f a)] g a₂ ↔ g a₁ =[ap f p; λ b : B, C b] g a₂ :=
begin 
  hinduction p, apply prod.mk,
  { intro q, rwr ap_idp },
  { intro q, exact pathover_of_pathover_ap C f q } 
end 

@[hott, hsimp]
def apo100 {A A' C : Type _} {f : A -> A'} {B : A' -> Type _} {a a' : A} (p : a = a') 
  {g : B (f a) -> B (f a) -> C} {g' : B (f a') -> B (f a') -> C} 
  (H : g =[p; λ a : A, B (f a) -> B (f a) -> C] g') :
  Π b₁ b₂ : B (f a), g b₁ b₂ = g' (ap f p ▸[B] b₁) (ap f p ▸[B] b₂) :=
begin 
  hinduction p, intros b₁ b₂, rwr tr_ap, rwr tr_ap,
  rwr idp_tr, rwr idp_tr, exact ap100 (eq_of_pathover_idp H) b₁ b₂ 
end

@[hott, hsimp]
def apo100' {A C : Type _} {B : A -> Type _} {a a' : A} (p : a = a') 
  {g : B a -> B a -> C} {g' : B a' -> B a' -> C} 
  (H : g =[p; λ a : A, B a -> B a -> C] g') :
  Π b₁ b₂ : B a, g b₁ b₂ = g' (p ▸[B] b₁) (p ▸[B] b₂) :=
begin 
  hinduction p, intros b₁ b₂, 
  rwr idp_tr, rwr idp_tr, exact ap100 (eq_of_pathover_idp H) b₁ b₂ 
end  

@[hott]
def ap01_tr2 {A B D : Type _} {C : B -> Type _} (f : A -> B) 
  (g : Π a : A, C (f a) -> C (f a) -> D) {a₁ a₂ : A} (p : a₁ = a₂) (c₁ c₂ : C (f a₁)) :
  g a₁ c₁ c₂ = g a₂ (ap f p ▸[λ b : B, C b] c₁) (ap f p ▸[λ b : B, C b] c₂) :=
begin hinduction p, hsimp end   

@[hott]
def apdd {A : Type _} {B : A -> Type _} {C : Type _}
  (f : Π (a : A) (b : B a), C) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} 
  (p : a₁ = a₂) (q : b₁ =[p] b₂) : f a₁ b₁ = f a₂ b₂ :=
begin hinduction p, hinduction q, refl end 

@[hott]
def apdd_inj_eq {A : Type _} {B : A -> Type _} {C : Type _}
  (f : Π (a : A) (b : B a), C) (f₁ : C -> A) 
  (f₂ : Π c : C, B (f₁ c)) 
  (inj : Π (c : C), c = f (f₁ c) (f₂ c)) {c₁ c₂ : C} :
Π (e : c₁ = c₂), e = (inj c₁) ⬝ (apdd f (ap f₁ e) 
                     ((apo01 f₁ f₂ e).1 (apd f₂ e))) ⬝ (inj c₂)⁻¹ :=
begin intro e, hinduction e, hsimp end

@[hott]
def apdd2 {A : Type _} {B C : A -> Type _} {D : Type _}
  (f : Π (a : A) (b : B a) (c : C a), D)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} {c₂ : C a₂}
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r : c₁ =[p] c₂) : f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
begin hinduction p, hinduction q, hinduction r, refl end  

@[hott]
def apdd2_inj_eq {A : Type _} {B C : A -> Type _} {D : Type _}
  (f : Π (a : A) (b : B a) (c : C a), D) (f₁ : D -> A) 
  (f₂ : Π d : D, B (f₁ d)) (f₃ : Π d : D, C (f₁ d)) 
  (inj : Π (d : D), d = f (f₁ d) (f₂ d) (f₃ d)) {d₁ d₂ : D} :
Π (e : d₁ = d₂), e = (inj d₁) ⬝ (apdd2 f (ap f₁ e) 
  ((apo01 f₁ f₂ e).1 (apd f₂ e)) ((apo01 f₁ f₃ e).1 (apd f₃ e))) 
  ⬝ (inj d₂)⁻¹ :=
begin intro e, hinduction e, hsimp end        

@[hott]
def ap_ap01 {A B : Type _} (f : A -> B) {a₁ a₂ : A} (pA : a₁ = a₂)
  (g : B -> A) (HP : Π a : A, g (f a) = a) :
  ap g (ap f pA) = (HP a₁) ⬝ pA ⬝ (HP a₂)⁻¹ :=
begin hinduction pA, rwr con_idp, rwr con.right_inv end

@[hott]
def ap_apd011 {A C : Type _} {B : A -> Type _} (f : Π (a : A), B a -> C) {a₁ a₂ : A} 
  {b₁ : B a₁} {b₂ : B a₂} (pA : a₁ = a₂) (pB : b₁ =[pA] b₂) (g : C -> A) 
  (HP : Π a b, g (f a b) = a) : 
  ap g (apd011 f pA pB) = (HP a₁ b₁) ⬝ pA ⬝ (HP a₂ b₂)⁻¹ :=
begin hinduction pA, hinduction pB, rwr con_idp, rwr con.right_inv end 

@[hott]
def ap_apd0111 {A D : Type _} {B : A -> Type _} {C : Π (a : A), B a -> Type _} 
  (f : Π (a : A) (b : B a) (c : C a b), D) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (pA : a₁ = a₂) 
  (pB : b₁ =[pA] b₂) (pC : c₁ =[apd011 C pA pB; id] c₂) 
  (g : D -> A) (HP : Π a b c, g (f a b c ) = a) : 
  ap g (apd0111 f pA pB pC) = (HP a₁ b₁ c₁) ⬝ pA ⬝ (HP a₂ b₂ c₂)⁻¹ :=
begin 
  hinduction pA, hinduction pB, hinduction pC, rwr con_idp, rwr con.right_inv 
end 

@[hott]
def ap_apd0111' {A D : Type _} {B C : A -> Type _} 
  (f : Π (a : A), B a -> C a -> D) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  {c₁ : C a₁} {c₂ : C a₂} (pA : a₁ = a₂) (pB : b₁ =[pA] b₂) (pC : c₁ =[pA] c₂) 
  (g : D -> A) (HP : Π a b c, g (f a b c ) = a) : 
  ap g (apd0111' f pA pB pC) = (HP a₁ b₁ c₁) ⬝ pA ⬝ (HP a₂ b₂ c₂)⁻¹ :=
begin 
  hinduction pA, hinduction pB, hinduction pC, rwr con_idp, rwr con.right_inv 
end 

@[hott]
def apd0111_eq {A D : Type _} {B : A -> Type _} {C : Π (a : A), B a -> Type _} 
  (f : Π (a : A) (b : B a) (c : C a b), D) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {pA pA': a₁ = a₂} {pB : b₁ =[pA] b₂} {pB' : b₁ =[pA'] b₂} 
  {pC : c₁ =[apd011 C pA pB; id] c₂} {pC' : c₁ =[apd011 C pA' pB'; id] c₂}
  (HpA : pA = pA') (HpB : pB =[HpA; λ x : a₁ = a₂, b₁ =[x] b₂] pB')
  (HpC : pC =[apd011 (λ (x : a₁ = a₂) (y : b₁ =[x] b₂), apd011 (λ a b, C a b) x y) HpA HpB;
                λ Hf : C a₁ b₁ = C a₂ b₂, c₁ =[Hf; id] c₂] pC') : 
  apd0111 f pA pB pC = apd0111 f pA' pB' pC' :=
begin hinduction HpA, hinduction HpB, hinduction HpC, refl end                 

@[hott]
def apdo0111 {A : Type _} {B C : A -> Type _} {D : Π a : A, B a -> Type _}
  (f : Π (a : A) (b : B a) (d : D a b), C a)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂}
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r : d₁ =[apd011 D p q; id] d₂) :
  f a₁ b₁ d₁ =[p] f a₂ b₂ d₂ :=
begin hinduction p, hinduction q, hinduction r, refl end 

@[hott, hsimp, reducible]
def apd01111 {A F : Type _} {B C D E : A -> Type _} 
  (h : Π a : A, B a -> C a -> D a -> E a -> F) {a a' : A} 
  {b : B a} {b' : B a'} {c : C a} {c' : C a'} {d : D a} {d' : D a'} 
  {e : E a} {e' : E a'}  
  (pA : a = a') (pB : b =[pA] b') (pC : c =[pA] c') (pD : d =[pA] d') 
  (pE : e =[pA] e') :
  h a b c d e = h a' b' c' d' e' :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD,
      hinduction pE, refl end 

@[hott, hsimp, reducible]
def apd01111' {A F : Type _} {B C D : A -> Type _} 
  (h : Π a : A, B a -> C a -> D a  -> F) {a a' : A} 
  {b : B a} {b' : B a'} {c : C a} {c' : C a'} {d : D a} {d' : D a'}  
  (pA : a = a') (pB : b =[pA] b') (pC : c =[pA] c') (pD : d =[pA] d') :
  h a b c d = h a' b' c' d' :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD, refl end

@[hott, hsimp, reducible]
def ap_apd01111' {A F : Type _} {B C D : A -> Type _} 
  (h : Π a : A, B a -> C a -> D a  -> F) {a a' : A} 
  {b : B a} {b' : B a'} {c : C a} {c' : C a'} {d : D a} {d' : D a'}  
  (pA : a = a') (pB : b =[pA] b') (pC : c =[pA] c') (pD : d =[pA] d') 
  (g : F -> A) (HP : Π a b c d, g (h a b c d) = a) :
  ap g (apd01111' h pA pB pC pD) = (HP a b c d) ⬝ pA ⬝ (HP a' b' c' d')⁻¹ :=
begin 
  hinduction pA, hinduction pB, hinduction pC, hinduction pD, rwr con_idp, 
  rwr con.right_inv 
end

@[hott]
def apd01111_v2 {A E : Type _} {B : A -> Type _} {C D : Π (a : A), B a -> Type _} 
  (f : Π (a : A) (b : B a) (c : C a b) (d : D a b), E) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂} (pA : a₁ = a₂) 
  (pB : b₁ =[pA] b₂) (pC : c₁ =[apd011 C pA pB; id] c₂) (pD : d₁ =[apd011 D pA pB; id] d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD, refl end

@[hott] 
def ap_apd01111_v2 {A E : Type _} {B : A -> Type _} {C D : Π (a : A), B a -> Type _} 
  (f : Π (a : A) (b : B a) (c : C a b) (d : D a b), E) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂} (pA : a₁ = a₂) 
  (pB : b₁ =[pA] b₂) (pC : c₁ =[apd011 C pA pB; id] c₂) (pD : d₁ =[apd011 D pA pB; id] d₂) 
  (g : E -> A) (HP : Π a b c d, g (f a b c d) = a) : 
  ap g (apd01111_v2 f pA pB pC pD) = (HP a₁ b₁ c₁ d₁) ⬝ pA ⬝ (HP a₂ b₂ c₂ d₂)⁻¹ :=
begin 
  hinduction pA, hinduction pB, hinduction pC, hinduction pD, rwr con_idp, 
  rwr con.right_inv 
end

@[hott]
def apd000011 {A B C F : Type _} {D : B -> A -> Type _} {E : C -> A -> Type _} 
  (f : Π (a : A) (b : B) (c : C), D b a -> E c a -> F) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
  {d₁ : D b₁ a₁} {d₂ : D b₂ a₂} {e₁ : E c₁ a₁} {e₂ : E c₂ a₂} (pa : a₁ = a₂) (pb : b₁ = b₂)
  (pc : c₁ = c₂) (pd : d₁ =[ap011 D pb pa; id] d₂) (pe : e₁ =[ap011 E pc pa; id] e₂) : 
  f a₁ b₁ c₁ d₁ e₁ = f a₂ b₂ c₂ d₂ e₂ :=
begin hinduction pa, hinduction pb, hinduction pc, hinduction pd, hinduction pe, refl end  

@[hott]
def apd01d6 {A H : Type _} {B : A -> Type _} {C D: Π (a : A), B a -> Type _}
  {E F G : Π (a : A) (b : B a), C a b -> D a b -> Type _} (f : Π (a : A) (b : B a) 
  (c : C a b) (d : D a b), E a b c d -> F a b c d -> G a b c d -> H)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} 
  {d₂ : D a₂ b₂} {e₁ : E a₁ b₁ c₁ d₁} {e₂ : E a₂ b₂ c₂ d₂} {f₁ : F a₁ b₁ c₁ d₁} 
  {f₂ : F a₂ b₂ c₂ d₂} {g₁ : G a₁ b₁ c₁ d₁} {g₂ : G a₂ b₂ c₂ d₂} 
  (pA : a₁ = a₂) (pB : b₁ =[pA] b₂) (pC : c₁ =[apd011 C pA pB; id] c₂) 
  (pD : d₁ =[apd011 D pA pB; id] d₂) (pE : e₁ =[apd01111_v2 E pA pB pC pD; id] e₂)
  (pF : f₁ =[apd01111_v2 F pA pB pC pD; id] f₂) 
  (pG : g₁ =[apd01111_v2 G pA pB pC pD; id] g₂) :
  f a₁ b₁ c₁ d₁ e₁ f₁ g₁ = f a₂ b₂ c₂ d₂ e₂ f₂ g₂ :=
begin 
  hinduction pA, hinduction pB, hinduction pC, hinduction pD, hinduction pE, 
  hinduction pF, hinduction pG, refl 
end 

@[hott]
def ap_apd01d6 {A H : Type _} {B : A -> Type _} {C D: Π (a : A), B a -> Type _}
  {E F G : Π (a : A) (b : B a), C a b -> D a b -> Type _} (f : Π (a : A) (b : B a) 
  (c : C a b) (d : D a b), E a b c d -> F a b c d -> G a b c d -> H)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} 
  {d₂ : D a₂ b₂} {e₁ : E a₁ b₁ c₁ d₁} {e₂ : E a₂ b₂ c₂ d₂} {f₁ : F a₁ b₁ c₁ d₁} 
  {f₂ : F a₂ b₂ c₂ d₂} {g₁ : G a₁ b₁ c₁ d₁} {g₂ : G a₂ b₂ c₂ d₂} 
  (pA : a₁ = a₂) (pB : b₁ =[pA] b₂) (pC : c₁ =[apd011 C pA pB; id] c₂) 
  (pD : d₁ =[apd011 D pA pB; id] d₂) (pE : e₁ =[apd01111_v2 E pA pB pC pD; id] e₂)
  (pF : f₁ =[apd01111_v2 F pA pB pC pD; id] f₂) 
  (pG : g₁ =[apd01111_v2 G pA pB pC pD; id] g₂) (g : H -> A) 
  (pH : Π a' b' c' d' e' f' g', g (f a' b' c' d' e' f' g') = a') : 
  ap g (apd01d6 f pA pB pC pD pE pF pG) = (pH a₁ b₁ c₁ d₁ e₁ f₁ g₁) ⬝ pA ⬝ 
                                          (pH a₂ b₂ c₂ d₂ e₂ f₂ g₂)⁻¹ :=
begin 
  hinduction pA, hinduction pB, hinduction pC, hinduction pD, hinduction pE, 
  hinduction pF, hinduction pG, rwr con_idp, rwr con.right_inv 
end                                          

@[hott]
def apd01111_eq {A F : Type _} {B C D E : A -> Type _} 
  (h : Π a : A, B a -> C a -> D a -> E a -> F) {a a' : A} 
  {b : B a} {b' : B a'} {c : C a} {c' : C a'} {d : D a} {d' : D a'} 
  {e : E a} {e' : E a'}  
  {pA pA' : a = a'} {pB : b =[pA] b'} {pB' : b =[pA'] b'} {pC : c =[pA] c'} 
  {pC' : c =[pA'] c'} {pD : d =[pA] d'} {pD' : d =[pA'] d'} 
  {pE : e =[pA] e'} {pE' : e =[pA'] e'} (pA_eq : pA = pA') 
  (pB_eq : pB =[pA_eq; λ q : a = a', b =[q] b'] pB') 
  (pC_eq : pC =[pA_eq; λ q : a = a', c =[q] c'] pC') 
  (pD_eq : pD =[pA_eq; λ q : a = a', d =[q] d'] pD')
  (pE_eq : pE =[pA_eq; λ q : a = a', e =[q] e'] pE') :
  apd01111 h pA pB pC pD pE = apd01111 h pA' pB' pC' pD' pE' :=
begin hinduction pA_eq, hinduction pB_eq, hinduction pC_eq, hinduction pD_eq, 
      hinduction pE_eq, refl end 

@[hott]
def apdo01111 {A : Type _} {B E : A -> Type _} {C D : Π a : A, B a -> Type _}
  (f : Π (a : A) (b : B a), C a b -> D a b -> E a)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
  {d₁ : D a₁ b₁} {d₂ : D a₂ b₂}
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r₁ : c₁ =[apd011 C p q; id] c₂) 
  (r₂ : d₁ =[apd011 D p q; id] d₂) :
  f a₁ b₁ c₁ d₁ =[p] f a₂ b₂ c₂ d₂ :=
begin hinduction p, hinduction q, hinduction r₁, hinduction r₂, refl end 

@[hott]
def apdo011111 {A : Type _} {B C F : A -> Type _} {D E : Π a : A, B a -> C a -> Type _}
  (f : Π (a : A) (b : B a) (c : C a), D a b c -> E a b c -> F a)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} {c₂ : C a₂} {d₁ : D a₁ b₁ c₁} 
  {d₂ : D a₂ b₂ c₂} {e₁ : E a₁ b₁ c₁} {e₂ : E a₂ b₂ c₂}(p : a₁ = a₂) (q₁ : b₁ =[p] b₂)
  (q₂ : c₁ =[p] c₂) (r₁ : d₁ =[apd0111' D p q₁ q₂; id] d₂) 
  (r₂ : e₁ =[apd0111' E p q₁ q₂; id] e₂) :
  f a₁ b₁ c₁ d₁ e₁ =[p] f a₂ b₂ c₂ d₂ e₂ :=
begin hinduction p, hinduction q₁, hinduction q₂, hinduction r₁, hinduction r₂, refl end 

@[hott]
def tr_fn_tr_eval {A B : Type _} {C : A -> B -> Type _} {a₁ a₂ : A}
  (f : Π (b : B), C a₁ b) (p : a₁ = a₂) (b : B) :
  (p ▸ f) b = p ▸ (f b) :=
begin hinduction p, refl end 

@[hott]
def tr_fn_ev_tr_fn_ev {A B : Type _} {C : A -> Type _} {a₁ a₂ : A} {b : B} 
  (p : a₁ = a₂) (g : Π (a : A), B -> C a) : p ▸ ((g a₁) b) = (p ▸ (g a₁)) b :=
begin hinduction p, refl end  

@[hott]
def fn_tr_tr_ev {A : Type _} {B C : A -> Type _} (f : Π {a : A}, B a -> C a) {a₁ a₂ : A}
  (p : a₁ = a₂) (b₁ : B a₁) : f (p ▸ b₁) = p ▸ (f b₁) :=
begin hinduction p, refl end  

@[hott]
def fn2_tr_tr_ev {A B : Type _} {C D : A -> B -> Type _} 
  (f : Π (a : A) (b : B), C a b -> D a b) {b₁ b₂ : B} (p : b₁ = b₂) (a : A) (c : C a b₁) :
  f a b₂ (p ▸ c) = p ▸ (f a b₁ c) :=
begin hinduction p, refl end

@[hott]
def tr_fn2_ev_fn2_ev_tr_tr {A : Type _} {B C D : A -> Type _} {a₁ a₂ : A} (p : a₁ = a₂)
  (b₁ : B a₁) (c₁ : C a₁) (f : Π (a : A) (b : B a) (c : C a), D a) :
  p ▸ f a₁ b₁ c₁ = f a₂ (p ▸ b₁) (p ▸ c₁) :=
begin hinduction p, refl end 

@[hott]
def tr_fn_eval_tr {A B C : Type _} {f : A -> C} (p : A = B) (b : B) : 
  (p ▸ f) b = f (p⁻¹ ▸ b) := 
begin hinduction p, refl end

@[hott]
def tr_fn_eval_tr' {A B : Type _} (g : B -> Type _) {b₁ b₂ : B} (p : b₁ = b₂) (a : A) 
  (f : A -> g b₁) : (p ▸ f) a = p ▸ (f a) := 
begin hinduction p, refl end 

@[hott]
def tr_dep_fn_eval_tr {A C : Type _} {B : A -> Type _}  
  {a₁ a₂ : A} {f : B a₁ -> C} (p : a₁ = a₂) (b : B a₂) : (p ▸ f) b = f (p⁻¹ ▸ b) :=
begin hinduction p, refl end  

@[hott]
def tr_fn2_eval_tr {A : Type _} {B C D : A -> Type _}  
  {a₁ a₂ : A} (f₁ : B a₁ -> C a₁ -> D a₁) (p : a₁ = a₂) (b₂ : B a₂) 
  (c₂ : C a₂) : 
  (p ▸ f₁) b₂ c₂ = p ▸ f₁ (p⁻¹ ▸ b₂) (p⁻¹ ▸ c₂) :=
begin hinduction p, refl end 

@[hott]
def tr_dep_fn2_eval_tr {A C : Type _} {B : A -> Type _}  
  {a₁ a₂ : A} (f₂ : B a₂ -> B a₂ -> C) (p : a₁ = a₂) (b₁ b₂ : B a₁) : 
  (p⁻¹ ▸ f₂) b₁ b₂ = f₂ (p ▸ b₁) (p ▸ b₂) :=
begin hinduction p, refl end 

@[hott]
def tr_fn2_tr_ev {A : Type _} {B C D : A -> Type _} {a₁ a₂ : A} 
  (f₁ : B a₁ -> C a₁ -> D a₁) (p : a₁ = a₂) (b₁ : B a₁) (c₁ : C a₁) : 
  p ▸ f₁ b₁ c₁ = (p ▸ f₁) (p ▸ b₁) (p ▸ c₁) :=
begin hinduction p, refl end 

@[hott]
def ap100_tr {A B C : Type _} {F G : A -> B -> C} {D : C -> Type _} 
  (p : F = G) {a : A} {b : B} (f : D (F a b)) :
  (ap100 p a b ▸[λ c : C, D c] f) = (p ▸[λ H : A -> B -> C, D (H a b)] f) :=
begin hinduction p, refl end

@[hott]
def ap100_tr_comp {A C : Type _} {F G : A -> A -> C} {D : C -> Type _} 
  (p : F = G) {a b c : A} (f : Π  b c : A, D (F a b) -> D (F b c) -> D (F a c)) 
  (dab : D (G a b)) (dbc : D (G b c)) : 
  (ap100 p a c ▸[λ c : C, D c] (f b c ((ap100 p a b)⁻¹ ▸ dab) ((ap100 p b c)⁻¹ ▸ dbc))) = 
          ((p ▸[λ H : A -> A -> C, Π b c : A, D (H a b) -> D (H b c) -> D (H a c)] f) 
                                                                         b c dab dbc) :=
begin hinduction p, refl end

@[hott] 
def tr_ap011 {A B C : Type _} {x₁ y₁ : A} {x₂ y₂ : B} {P : C → C -> Type _} (f : A -> B -> C) 
  (g : Π c : C, P c c) (p : x₁ = y₁) (q : x₂ = y₂) :
  (ap011 f p q) ▸[λ c : C, P (f x₁ x₂) c] (g (f x₁ x₂)) = 
  (p ▸[λ a : A, P (f x₁ x₂) (f a y₂)] (q ▸[λ b : B, P (f x₁ x₂) (f x₁ b)] g (f x₁ x₂))) :=
begin hinduction p, hinduction q, refl end

@[hott]
def tr_tr_pair {A B : Type _} {P : A -> A -> Type _} (f : Π a : A, P a a) 
  {Q : B -> B -> Type _} (g : Π b : B, Q b b) {a₁ a₂ : A} {b₁ b₂ : B} (p : a₁ = a₂) (q : b₁ = b₂) : 
  p ▸[λ x : A, (P a₁ x) × (Q b₁ b₂)] (q ▸[λ y : B, (P a₁ a₁) × (Q b₁ y)] (f a₁, g b₁)) = 
  (p ▸[λ x : A, P a₁ x] (f a₁), q ▸[λ y : B, Q b₁ y] (g b₁)) :=
begin hinduction p, hinduction q, refl end   

@[hott]
def ap_tr_fn {A : Type _} {B : A -> Type _} (f : A -> A) (h : Π a : A, B a -> B (f a)) 
  {a₁ a₂ : A} (p : a₁ = a₂) (b : B a₁) : (ap f p) ▸ (h a₁ b) = h a₂ (p ▸ b) :=
begin hinduction p, refl end  

@[hott]
def tr_ap_id {A : Type _} {B : A -> Type _} {a₁ a₂ : A} (p : a₁ = a₂) (b₁ : B a₁) :
  p ▸[λ a, B a] b₁ = ((ap B p) ▸[λ b, b] b₁) :=
tr_compose (λ b : Type _, b) B p b₁  

@[hott]
def fn_ev_tr_tr_fn_ev {A : Type _} {B C : A -> Type _} {f : Π (a : A), B a -> C a} 
  {a a' : A} (p : a = a') (b : B a) : f a' (p ▸ b) = p ▸ (f a b) :=
begin hinduction p, refl end  

@[hott]
def tr_fn_fn_ev_fn_tr_fn {A B : Type _} {C D : A -> Type _} {a₁ a₂ : A} {b : B} 
  (p : a₁ = a₂) (g : Π (a : A), B -> C a) (f : Π (a : A), C a -> D a) : 
  p ▸ f a₁ ((g a₁) b) = f a₂ ((p ▸ (g a₁)) b) :=
begin hinduction p, refl end  

@[hott]
def po_fn_ev {A B : Type _} {C : A -> B -> Type _} {a₁ a₂ : A} 
  {f₁ : Π b : B, C a₁ b} {f₂ : Π b : B, C a₂ b} (p : a₁ = a₂) (b : B) :
  f₁ =[p; λa : A, Π b : B, C a b ] f₂ -> f₁ b =[p; λ a : A, C a b] f₂ b :=
begin 
  hinduction p, intro po, hinduction po, 
  apply pathover_idp_of_eq, refl 
end  

@[hott]
def homotopy_eq_rinv {A B : Type _} {f g : A -> B} {H : f ~ g} :
  apd10 (eq_of_homotopy H) = H :=
@is_equiv.right_inv _ _ _ (eq_equiv_homotopy f g).to_is_equiv H  

@[hott]
def deq_of_homotopy {A : Type _} {h₁ h₂ : A -> Type _} {p : h₁ = h₂} {g₁ : Π a : A, h₁ a}
  {g₂ : Π a : A, h₂ a} : 
  (Π a : A, g₁ a =[ap10 p a; id] g₂ a) -> g₁ =[p; λ h : A -> Type _, Π a : A, h a] g₂ :=
begin 
  hinduction p, hsimp, intro hty, apply pathover_idp_of_eq, 
  exact eq_of_homotopy (λ a : A, eq_of_pathover_idp (hty a)) 
end  

@[hott]
def deq_of_homotopy2 {A : Type _} {B C D : A -> Type _} {a₁ a₂ : A} {p : a₁ = a₂}
  {f₁ : B a₁ -> C a₁ -> D a₁} {f₂ : B a₂ -> C a₂ -> D a₂} :
  (Π (b₁ : B a₁) (c₁ : C a₁), f₁ b₁ c₁ =[p] f₂ (p ▸ b₁) (p ▸ c₁)) -> 
                                                  f₁ =[p; λ a : A, B a -> C a -> D a] f₂ :=
begin 
  hinduction p, hsimp, intro hty, apply pathover_idp_of_eq, 
  exact eq_of_homotopy2 (λ (b₁ : B a₁) (c₁ : C a₁), eq_of_pathover_idp (hty b₁ c₁)) 
end                                                        

@[hott]
def deq_of_homotopy3 {A B C : Type _} {h₁ h₂ : A -> B -> C -> Type _} {p : h₁ = h₂} 
  {g₁ : Π (a : A) (b : B) (c : C), h₁ a b c} {g₂ : Π (a : A) (b : B) (c : C), h₂ a b c} : 
  (Π (a : A) (b : B) (c : C) , g₁ a b c =[ap1000 p a b c; id] g₂ a b c) -> 
              g₁ =[p; λ h : A -> B -> C -> Type _, Π (a : A) (b : B) (c : C), h a b c] g₂ :=
begin 
  hinduction p, hsimp, intro hty, apply pathover_idp_of_eq, 
  exact eq_of_homotopy3 (λ (a : A) (b : B) (c : C), eq_of_pathover_idp (hty a b c)) 
end  

@[hott]
def dep_eq_of_homotopy {A : Type _} {P : A -> A -> Type _} {b b' : A} (p : b = b') 
  (f : Π a : A, P b a) (f' : Π a : A, P b' a) : 
  (Π a : A, f a =[p; λ b : A, P b a] f' a) -> f =[p; λ b : A, Π a : A, P b a] f' :=
begin 
  hinduction p, 
  intro htp, apply pathover_idp_of_eq, apply eq_of_homotopy, 
  intro a, exact eq_of_pathover_idp (htp a) 
end  

@[hott]
def dep_eq_of_homotopy3 {A B C : Type _} {D : Π (b : B) (c : C), Type _} 
  {P : A -> B -> C -> Type _} {a a' : A} (p : a = a') 
  (f : Π (b : B) (c : C), D b c ->P a b c) (f' : Π (b : B) (c : C), D b c -> P a' b c) : 
  (Π (b : B) (c : C) (d : D b c), f b c d =[p; λ a'' : A, P a'' b c] f' b c d) -> 
                      f =[p; λ a'' : A, Π (b : B) (c : C), D b c -> P a'' b c] f' :=
begin 
  hinduction p, 
  intro htp, apply pathover_idp_of_eq, apply eq_of_homotopy3, 
  intros b c d, exact eq_of_pathover_idp (htp b c d) 
end 

@[hott]
def dep_set_eq_eq {A : Type _} {B : A -> Type _} {a a' : A} [is_set (B a')]
  (p : a = a') {b : B a} {b' : B a'} (f f' : b =[p] b') : f = f' :=
have tr_eq : tr_eq_of_pathover f = tr_eq_of_pathover f', from is_set.elim _ _,
let po_tr_eq := ap pathover_of_tr_eq tr_eq in
begin 
  let F := (pathover_equiv_tr_eq p b b').to_fun,
  rwr <- is_equiv.left_inv F f,
  rwr <- is_equiv.left_inv F f',
  exact po_tr_eq
end  

/- Facts on combinations of pathovers and versions of `ap` and `apd`. -/
@[hott]
def pathover_ap10 {A : Type _} {h₁ h₂ : A -> Type _} {p : h₁ = h₂} {g₁ : Π a : A, h₁ a}
  {g₂ : Π a : A, h₂ a} : 
  Π a : A, g₁ a =[p; λ h : A -> Type _, h a] g₂ a -> g₁ a =[ap10 p a; id] g₂ a :=
begin hinduction p, intros a q₁, exact pathover_idp_of_eq _ (eq_of_pathover_idp q₁) end  

@[hott]
def pathover_ap1000 {A B C : Type _} {h₁ h₂ : A -> B -> C -> Type _} {p : h₁ = h₂} 
  {g₁ : Π a b c, h₁ a b c} {g₂ : Π a b c, h₂ a b c} : 
  Π a b c, g₁ a b c =[p; λ h : A -> B -> C -> Type _, h a b c] g₂ a b c -> 
           g₁ a b c =[ap1000 p a b c; id] g₂ a b c :=
begin hinduction p, intros a b c q, exact pathover_idp_of_eq _ (eq_of_pathover_idp q) end 

@[hott]
def pathover_of_pathover_ap100 {A B C: Type _} {D : C -> Type _} {h₁ h₂ : A -> B -> C} 
  {p : h₁ = h₂} : Π {a : A} {b : B} {c₁ : D (h₁ a b)} {c₂ : D (h₂ a b)}, 
  c₁ =[ap100 p a b; D] c₂ -> c₁ =[p; λ h : A -> B -> C, D (h a b)] c₂ :=
begin hinduction p, intros a b c₁ c₂ q, exact pathover_idp_of_eq _ (eq_of_pathover_idp q) end 

@[hott] def pathover_ap_idpo {A A' : Type _} (B' : A' → Type _) (f : A → A') {a : A}
    {b : B' (f a)} : pathover_ap B' f (@idpo _ _ a b) = idpo :=
begin refl end    

@[hott] 
def pathover_ap_concato {A A' : Type _}(B' : A' → Type _) (f : A → A') {a₁ a₂ a₃ : A}
    {p : a₁ = a₂} {q : a₂ = a₃} {b₁ : B' (f a₁)} {b₂ : B' (f a₂)} {b₃ : B' (f a₃)}
    {P : b₁ =[p; B' ∘ f] b₂} {Q : b₂ =[q; B' ∘ f] b₃} :
    pathover_ap B' f (P ⬝o Q) =[ap_con f p q; λ r : f a₁ = f a₃, b₁ =[r; B'] b₃] 
                                            pathover_ap B' f P ⬝o pathover_ap B' f Q :=
begin hinduction p, hinduction q, hinduction P, hinduction Q, exact idpo end

@[hott] 
def pathover_ap_inverseo {A A' : Type _}(B' : A' → Type _) (f : A → A') {a₁ a₂ : A}
    {p : a₁ = a₂} {b₁ : B' (f a₁)} {b₂ : B' (f a₂)} {P : b₁ =[p; B' ∘ f] b₂} :
    pathover_ap B' f (P⁻¹ᵒ) =[ap_inv f p; λ r : f a₂ = f a₁, b₂ =[r; B'] b₁] 
                                                            (pathover_ap B' f P)⁻¹ᵒ :=
begin hinduction p, hinduction P, exact idpo end

@[hott]
def po_of_po_apd100 {A : Type _} {B : A -> Type _} {C : Π (a : A), B a -> Type _}
  {a₀ : A} {b₀ : B a₀} {D : C a₀ b₀ -> Type _} 
  {f g : Π (a : A) (b : B a), C a b} (p : f = g) (df : D (f a₀ b₀)) 
  (dg : D (g a₀ b₀)) : (df =[apd100 p a₀ b₀; λ c, D c] dg) -> 
                        df =[p; λ h : Π (a : A) (b : B a), C a b, D (h a₀ b₀)] dg :=
begin 
  hinduction p,
  have q : apd100 (refl f) a₀ b₀ = refl (f a₀ b₀), from rfl, 
  rwr q, intro po_apd, apply pathover_idp_of_eq, exact eq_of_pathover_idp po_apd 
end

@[hott]
def po_homotopy_of_tr_eq2 {A B : Type _} {f g : A -> B} (p : f = g) 
  {Q : B -> B -> Type _} {a₁ a₂ : A} (hf : Q (f a₁) (f a₂)) (hg : Q (g a₁) (g a₂)) :
  (apd10 p a₂) ▸[λ b, Q (g a₁) b] ((apd10 p a₁) ▸[λ b, Q b (f a₂)] hf) = hg -> 
  hf =[p; λ f' : A -> B, Q (f' a₁) (f' a₂)] hg :=
begin hinduction p, hsimp, intro H, apply pathover_idp_of_eq, exact H end  

@[hott]
def apd011_idp_to_ap {A C : Type _} {B : A -> Type _} (f : Π (a : A), B a -> C) {a : A} 
  {b₁ b₂ : B a} (q : b₁ =[idp] b₂) : apd011 f idp q = ap (f a) (eq_of_pathover_idp q) :=
begin hinduction q, change idp = idp, exact idp end  

/- Some facts involving equivalences -/
@[hott]
def dep_cast {A B : Type _} (e : A ≃ B) (P : B -> Type _) :
  (∀ b : B, P b) -> ∀ a : A, P (e a) :=
assume Pb a, Pb (e a)   

@[hott]
def dep_cast_inv {A : Type u} {B : Type v} (e : A ≃ B) (P : B -> Type w) :
  (∀ a : A, P (e a)) -> ∀ b : B, P b :=
begin intros Pa b, rwr <- is_equiv.right_inv e b, apply Pa end 

@[hott]
def ap_inv_po_fn {A : Type u} {B : Type v} {P : A -> Type w} {a₁ a₂ : A} (f : P a₁ -> B) 
  (H : ∀ a₁ a₂ : A, is_equiv (@ap _ _ P a₁ a₂)) : ∀ (b : P a₂) (p : P a₁ = P a₂), 
  ((@is_equiv.inv _ _ _ (H a₁ a₂) p) ▸[λ a : A, P a -> B] f) b = 
              (p ▸[λ C : Type w, C -> B] f) b :=
begin 
  let e := equiv.mk (@ap _ _ P a₁ a₂) (H a₁ a₂),
  assume b, fapply dep_cast_inv e, intro q, hinduction q, 
  change (e⁻¹ᶠ (e (refl a₁))▸[λ (a : A), P a → B] f) b = 
         (ap P (refl a₁)▸[λ (C : Type w), C → B] f) b,
  rwr is_equiv.left_inv e (refl a₁)
end  

/- Lift of trunctypes, in particular propositions and sets. -/
@[hott]
def trunctype_ulift {n : ℕ₋₂} : trunctype.{u} n -> trunctype.{(max u' u)} n := 
  assume trunctype_u, 
  trunctype.mk (ulift.{u' u} ↥trunctype_u) (@is_trunc_lift ↥trunctype_u n _)

/- We prove some lemmas on universe lifting. -/
@[hott]
def down_up_eq {A : Type u} (x : A) : (ulift.up.{v} x).down = x := idp

@[hott]
def up_down_eq {A : Type u} (x : ulift.{v u} A) : ulift.up.{v} x.down = x := 
begin hinduction x, hsimp end

@[hott]
def ulift_equiv {A : Type u} : ulift.{v u} A ≃ A :=
  equiv.mk ulift.down (adjointify ulift.down ulift.up down_up_eq up_down_eq)

@[hott]
def down_eq_up {A : Type u} (x : ulift.{v u} A) (y : A) : 
  x.down = y -> x = ulift.up y :=
begin hinduction x, intro H, rwr down_up_eq down at H, exact ap ulift.up H end

/- The calculation rules for dependent if-then-else `dite` are missing in 
   [hott.init.logic]: Instances of the decision-clause may be not equal, and then the 
   eliminator `decidable.rec` does not work. This problem vanishes if the decision-clause 
   is a proposition. -/
@[hott] def dif_pos {c : Type _} [is_prop c] [H : decidable c] (Hc : c) {A : Type _} 
  {t : c -> A} {e : ¬c -> A} : (dite c t e) = t Hc :=
decidable.rec
  (λ Hc' : c,    calc (@dite c (decidable.inl Hc') A t e) = t Hc' : rfl
                      ... = t Hc : ap t (is_prop.elim _ _)) 
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

@[hott] def dif_neg {c : Type _} [is_prop c] [H : decidable c] (Hnc : ¬c) {A : Type _} {t : c -> A} 
  {e : ¬c -> A} : (dite c t e) = e Hnc :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc' : ¬c, calc @dite c (decidable.inr Hnc') A t e = e Hnc' : rfl 
                     ... = e Hnc : ap e (is_prop.elim _ _))
  H   

/- We need some equivalent descriptions of equalities of functions. -/
@[hott, hsimp]
def fn2_deq_to_eval_eq {A C : Type _} {B : A -> Type _} {a b : A} 
  {f : (B a) -> (B a) -> C} {g : (B b) -> (B b) -> C} (p : a = b) :
  (Π (a₁ a₂ : B a), f a₁ a₂ = g (p ▸ a₁) (p ▸ a₂)) -> 
                                  f =[p; λ c : A, (B c) -> (B c) -> C] g :=
begin 
  hinduction p, change (Π (a₁ a₂ : B a), f a₁ a₂ = g a₁ a₂) -> _, intro Pₕ,
  apply pathover_of_tr_eq, exact eq_of_homotopy2 Pₕ 
end  

@[hott, hsimp]
def fn2_eval_eq_to_deq {A C : Type _} {B : A -> Type _} {a b : A} 
  {f : (B a) -> (B a) -> C} {g : (B b) -> (B b) -> C} (p : a = b) :
  (f =[p; λ c : A, (B c) -> (B c) -> C] g) -> 
                    (Π (a₁ a₂ : B a), f a₁ a₂ = g (p ▸ a₁) (p ▸ a₂)) :=
begin 
  hinduction p, intro pₕ, exact ap100 (eq_of_pathover_idp pₕ)
end

@[hott]
def fn2_deq_eval_eq_rinv {A C : Type _} {B : A -> Type _} {a b : A} 
  {f : (B a) -> (B a) -> C} {g : (B b) -> (B b) -> C} (p : a = b)
  (Pₕ : Π (a₁ a₂ : B a), f a₁ a₂ = g (p ▸ a₁) (p ▸ a₂)) : 
  fn2_eval_eq_to_deq p (fn2_deq_to_eval_eq p Pₕ) = Pₕ :=
begin hinduction p, hsimp, rwr ap100_eq_of_hty2_inv end   

@[hott]
def fn2_deq_eval_eq_linv {A C : Type _} {B : A -> Type _} {a b : A} 
  {f : (B a) -> (B a) -> C} {g : (B b)  -> (B b) -> C} (p : a = b)
  (pₕ : f =[p; λ a : A, (B a) -> (B a) -> C] g) : 
  fn2_deq_to_eval_eq p (fn2_eval_eq_to_deq p pₕ) = pₕ :=
begin 
  hinduction p, hsimp, rwr hty2_of_ap100_eq_inv, 
  change pathover_idp_of_eq (λ (a : A), (B a) → (B a) → C) (eq_of_pathover_idp pₕ) = pₕ,
  rwr pathover_idp_of_eq_eq_of_pathover_idp 
end

@[hott]
def fn2_po_adp011_idp_eq {A : Type _} {B : A -> Type _} {C : Π a : A, B a -> Type _} 
  {a : A} {b₁ b₂ : B a} (p : b₁ = b₂) {f₁ : C a b₁} {f₂ : C a b₂} : 
  f₁ =[p] f₂ -> f₁ =[apd011 C (refl a) (pathover_idp_of_eq B p); id] f₂ :=
begin hinduction p, intro q, apply pathover_idp_of_eq, exact eq_of_pathover_idp q end

@[hott]
def fn2_po_of_tr_eq {A C : Type _} {b₁ b₂ : A -> A -> C} (p : b₁ = b₂) {D : C -> Type _}
  {f₁ : Π a : A, D (b₁ a a)} {f₂ : Π a : A, D (b₂ a a)} : 
  (Π a : A, ap100 p a a ▸ f₁ a = f₂ a) -> 
  @pathover (A -> A -> C) b₁ (λ b : A -> A -> C, Π a : A, D (b a a)) f₁ b₂ p f₂ :=
begin hinduction p, intro q, apply pathover_idp_of_eq, exact eq_of_homotopy q end  

@[hott]
def fn2_po_of_tr_eq' {A C : Type _} {b₁ b₂ : A -> A -> C} (p : b₁ = b₂) {D : C -> Type _}
  {f₁ : Π {a b c : A}, D (b₁ a b) -> D (b₁ b c) -> D (b₁ a c)} 
  {f₂ : Π {a b c : A}, D (b₂ a b) -> D (b₂ b c) -> D (b₂ a c)} : 
  (Π (a b c : A) (f : D (b₁ a b)) (g : D (b₁ b c)), ap100 p a c ▸ f₁ f g = 
                                          f₂ (ap100 p a b ▸ f) (ap100 p b c ▸ g)) -> 
  @pathover (A -> A -> C) b₁ (λ B : A -> A -> C, Π {a b c : A}, D (B a b) -> 
                                              D (B b c) -> D (B a c)) @f₁ b₂ p @f₂ :=
begin 
  hinduction p, intro q, apply pathover_idp_of_eq, apply eq_of_homotopy3, 
  intros a b c, exact eq_of_homotopy2 (q a b c) 
end

@[hott]
def tr_fn2_of_ap_tr_ap_tr {A B : Type _} {f g : A -> B} {a₁ a₂ : A} 
  (p : f = g) {C : B -> B -> Type _}  (h₁ : C (f a₁) (f a₂))
  (h₂ : C (g a₁) (g a₂)) : 
  (ap10 p a₂) ▸[λ b : B, C (g a₁) b] 
               ((ap10 p a₁) ▸[λ b : B, C b (f a₂)] h₁) = h₂ ->
               p ▸[λ f : A -> B, C (f a₁) (f a₂)] h₁ = h₂ :=
begin 
  hinduction p, rwr ap10_idp, rwr ap10_idp, 
  rwr idp_tr, rwr idp_tr, rwr idp_tr, intro q, assumption 
end

@[hott]
def eq_tr_tr {A : Type _} {P : A -> Type _} {a₁ a₂ : A} {p q : a₁ = a₂} (r : p = q) 
  (b : P a₁) : p ▸ b = q ▸ b := 
begin hinduction r, refl end

end hott