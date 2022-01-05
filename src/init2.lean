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

/- All these equalities should be produced by tactics. -/
@[hott]
def id_tr_eq_id_inv_con {A : Type _} {a₀ a₁ a₂ : A} (q : a₁ = a₂) (p : a₁ = a₀) :
  q ▸ p = q⁻¹ ⬝ p :=
begin hinduction q, rwr idp_tr, rwr idp_inv, rwr idp_con end  

@[hott]
def pathover_idp_of_id {A : Type _} : Π a : A, pathover_idp_of_eq id (@idp _ a) = idpo := 
  assume a, rfl

@[hott]
def ap0111 {A : Type u} {B : Type v} {C D : A -> B -> Type _} {E : Type _}
  (f : Π (a : A) (b : B), C a b -> D a b -> E)
  {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂}
  (p₁ : a₁ = a₂) (p₂ : b₁ = b₂) (p₃ : c₁ =[ap011 C p₁ p₂; id] c₂) 
  (p₄ : d₁ =[ap011 D p₁ p₂; id] d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ := 
begin hinduction p₁, hinduction p₂, hinduction p₃, hinduction p₄, refl end  

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

@[hott]
def apd000011 {A B C F : Type _} {D : B -> A -> Type _} {E : C -> A -> Type _} 
  (f : Π (a : A) (b : B) (c : C), D b a -> E c a -> F) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
  {d₁ : D b₁ a₁} {d₂ : D b₂ a₂} {e₁ : E c₁ a₁} {e₂ : E c₂ a₂} (pa : a₁ = a₂) (pb : b₁ = b₂)
  (pc : c₁ = c₂) (pd : d₁ =[ap011 D pb pa; id] d₂) (pe : e₁ =[ap011 E pc pa; id] e₂) : 
  f a₁ b₁ c₁ d₁ e₁ = f a₂ b₂ c₂ d₂ e₂ :=
begin hinduction pa, hinduction pb, hinduction pc, hinduction pd, hinduction pe, refl end  

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
def tr_fn_tr_eval {A B : Type _} {C : A -> B -> Type _} {a₁ a₂ : A}
  (f : Π (b : B), C a₁ b) (p : a₁ = a₂) (b : B) :
  (p ▸ f) b = p ▸ (f b) :=
begin hinduction p, refl end   

@[hott]
def tr_fn_eval_tr {A B C : Type _} {f : A -> C} (p : A = B) (b : B) : 
  (p ▸ f) b = f (p⁻¹ ▸ b) := 
begin hinduction p, refl end  

@[hott]
def tr_dep_fn_eval_tr {A C : Type _} {B : A -> Type _}  
  {a₁ a₂ : A} {f : B a₁ -> C} (p : a₁ = a₂) (b : B a₂) : (p ▸ f) b = f (p⁻¹ ▸ b) :=
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
def fn_ev_tr_tr_fn_ev {A : Type _} {B C : A -> Type _} {f : Π (a : A), B a -> C a} 
  {a a' : A} (p : a = a') (b : B a) : f a' (p ▸ b) = p ▸ (f a b) :=
begin hinduction p, refl end  

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

/- Facts on combinations of pathovers and versions of `ap`. -/
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

end hott