import hott.init set_theory

universes u v w
hott_theory

namespace hott

/- Should be in [init.path]. -/
notation eq `▸[`:50 P:0 `]`:0 b:50 := transport P eq b 

/- All these equalities should be produced by tactics. -/
@[hott]
def ap0111 {A : Type u} {B : Type v} {C D : A -> B -> Type _} {E : Type _}
  (f : Π (a : A) (b : B), C a b -> D a b -> E)
  {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂}
  (p₁ : a₁ = a₂) (p₂ : b₁ = b₂) (p₃ : c₁ =[ap011 C p₁ p₂; hott.set.id] c₂) 
  (p₄ : d₁ =[ap011 D p₁ p₂; hott.set.id] d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ := 
begin hinduction p₁, hinduction p₂, hinduction p₃, hinduction p₄, refl end  

@[hott]
def apd001 {A B D : Type _} {C : A -> B -> Type _} (f : Π (a : A) (b : B), C a b -> D) 
  {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
  (p₁ : a₁ = a₂) (p₂ : b₁ = b₂) (p₃ : c₁ =[ap011 C p₁ p₂; hott.set.id] c₂) : 
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
def apdd {A : Type _} {B C : A -> Type _} {D : Type _}
  (f : Π (a : A) (b : B a) (c : C a), D)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} {c₂ : C a₂}
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r : c₁ =[p] c₂) : f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
begin hinduction p, hinduction q, hinduction r, refl end 

@[hott]
def apo01 {A B : Type _} {C : B -> Type _} (f : A -> B) 
  (g : Π a : A, C (f a)) {a₁ a₂ : A} (p : a₁ = a₂) : 
  g a₁ =[p; λ a : A, C (f a)] g a₂ ↔ g a₁ =[ap f p; λ b : B, C b] g a₂ :=
begin 
  hinduction p, apply prod.mk,
  { intro q, rwr ap_idp },
  { intro q, exact pathover_of_pathover_ap C f q } 
end  

@[hott]
def apdd_inj_eq {A : Type _} {B C : A -> Type _} {D : Type _}
  (f : Π (a : A) (b : B a) (c : C a), D) (f₁ : D -> A) 
  (f₂ : Π d : D, B (f₁ d)) (f₃ : Π d : D, C (f₁ d)) 
  (inj : Π (d : D), d = f (f₁ d) (f₂ d) (f₃ d)) (d₁ d₂ : D) :
Π (e : d₁ = d₂), (inj d₁)⁻¹ ⬝ e ⬝ (inj d₂) = apdd f (ap f₁ e) 
        ((apo01 f₁ f₂ e).1 (apd f₂ e)) ((apo01 f₁ f₃ e).1 (apd f₃ e)) :=
begin intro e, hinduction e, hsimp, refl end        

@[hott]
def apdo0111 {A : Type _} {B C : A -> Type _} {D : Π a : A, B a -> Type _}
  (f : Π (a : A) (b : B a) (d : D a b), C a)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂}
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r : d₁ =[apd011 D p q; hott.set.id] d₂) :
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
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r₁ : c₁ =[apd011 C p q; hott.set.id] c₂) 
  (r₂ : d₁ =[apd011 D p q; hott.set.id] d₂) :
  f a₁ b₁ c₁ d₁ =[p] f a₂ b₂ c₂ d₂ :=
begin hinduction p, hinduction q, hinduction r₁, hinduction r₂, refl end 

@[hott]
def tr_fn_tr_eval {A B : Type _} {C : A -> B -> Type _} {a₁ a₂ : A}
  (f : Π (b : B), C a₁ b) (p : a₁ = a₂) (b : B) :
  (p ▸ f) b = p ▸ (f b) :=
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

end hott