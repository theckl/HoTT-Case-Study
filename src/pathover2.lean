import hott.init set_theory

universes u v w
hott_theory

namespace hott

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
def ap_11 {A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ B₀ B₁ C : Type u} 
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

end hott