import hott.init hott.types.trunc hott_def

universes u u' v w
hott_theory

namespace hott
open is_trunc trunc hott.is_equiv

/- All these equalities of pathovers, concatenations and transports of 
   identities should be produced by tactics. -/
@[hott]
def tr_eq_tr_to_eq {A : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} {b₁ c₁ : B a₁}
  (q : p ▸ b₁ = p ▸ c₁) : b₁ = c₁ :=
begin hinduction p, exact q end

@[hott]
def square_diag_id {A : Type _} {a b c d : A} : a = b -> a = c -> b = d -> c = d :=
 assume p q r, q⁻¹ ⬝ p ⬝ r

@[hott, hsimp]
def pathover_idp_of_eq_eq_of_pathover_idp {A : Type _} {B : A -> Type _} {a : A} 
  {b b': B a} (p : b =[idpath a] b') : pathover_idp_of_eq B (eq_of_pathover_idp p) = p :=
by hinduction p; refl

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
def pathover_of_tr_eq_inv {A : Type _} {B : A -> Type _} {a₁ a₂ : A} (p : a₁ = a₂)
  {b₁ : B a₁} {b₂: B a₂} (q : p ▸ b₁ = b₂) : 
  (pathover_of_tr_eq q)⁻¹ᵒ = pathover_of_tr_eq (inv_tr_eq_of_eq_tr q⁻¹) :=
begin hinduction p, hinduction q, refl end

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
def hty2_of_ap100_eq_inv {A B C : Type _} {f g : A → B -> C} (p : f = g) :
  eq_of_homotopy2 (ap100 p) = p :=
is_equiv.right_inv (funext.is_equiv_apd100 f g).inv p 

@[hott]
def apd011' {A C : Type _} {B : A -> Type _} (f : Π (a : A), B a -> C) {a₁ a₂ : A} 
  {b₁ : B a₁} (p : a₁ = a₂) : f a₁ b₁ = f a₂ (p ▸ b₁) :=
begin hinduction p, rwr idp_tr end

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
def apd011_idp_idpo {A : Type _} {B : A -> Type _} {C : Type _} 
  (f : Π (a : A), B a -> C) {a : A} {b : B a} :
  apd011 f (@idp _ a) (@idpo _ _ a b) = idp :=
idp

@[hott] 
def apd0111' {A : Type _} {B C : A -> Type _} {D : Type _} 
  (f : Π (a : A), B a -> C a → D) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} 
  {c₂ : C a₂} (Ha : a₁ = a₂) (Hb : b₁ =[Ha] b₂) (Hc : c₁ =[Ha] c₂) :
  f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
  begin hinduction Hb, hinduction Hc, refl end

@[hott]
def ap_4 {A B C D E : Type _} (f : A -> B -> C -> D -> E) {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C}
  {d₁ d₂ : D} (pA : a₁ = a₂) (pB : b₁ = b₂) (pC : c₁ = c₂) (pD : d₁ = d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD, refl end  

@[hott, hsimp]
def ap_6 {A B C D E F G : Type _} (g : A -> B -> C -> D -> E -> F -> G) {a₁ a₂ : A} 
  {b₁ b₂ : B} {c₁ c₂ : C} {d₁ d₂ : D} {e₁ e₂ : E} {f₁ f₂ : F} (pA : a₁ = a₂) 
  (pB : b₁ = b₂) (pC : c₁ = c₂) (pD : d₁ = d₂) (pE : e₁ = e₂) (pF : f₁ = f₂) :
  g a₁ b₁ c₁ d₁ e₁ f₁ = g a₂ b₂ c₂ d₂ e₂ f₂:=
begin 
  hinduction pA, hinduction pB, hinduction pC, hinduction pD, hinduction pE, 
  hinduction pF, refl 
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
def apdd2 {A : Type _} {B C : A -> Type _} {D : Type _}
  (f : Π (a : A) (b : B a) (c : C a), D)
  {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} {c₂ : C a₂}
  (p : a₁ = a₂) (q : b₁ =[p] b₂) (r : c₁ =[p] c₂) : f a₁ b₁ c₁ = f a₂ b₂ c₂ :=
begin hinduction p, hinduction q, hinduction r, refl end  

@[hott]
def ap_fn_eq {A B : Type _} {f g : A -> B} {a₁ a₂ : A} (q : f = g) (p : a₁ = a₂) :
  ap f p = ap10 q a₁ ⬝ ap g p ⬝ (ap10 q a₂)⁻¹ :=
begin hinduction q, change _ = idp ⬝ _ ⬝ idp, rwr idp_con end 

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
def apd01111_v2 {A E : Type _} {B : A -> Type _} {C D : Π (a : A), B a -> Type _} 
  (f : Π (a : A) (b : B a) (c : C a b) (d : D a b), E) {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
  {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} {d₁ : D a₁ b₁} {d₂ : D a₂ b₂} (pA : a₁ = a₂) 
  (pB : b₁ =[pA] b₂) (pC : c₁ =[apd011 C pA pB; id] c₂) (pD : d₁ =[apd011 D pA pB; id] d₂) :
  f a₁ b₁ c₁ d₁ = f a₂ b₂ c₂ d₂ :=
begin hinduction pA, hinduction pB, hinduction pC, hinduction pD, refl end

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
def tr_fn_eval_tr {A B C : Type _} {f : A -> C} (p : A = B) (b : B) : 
  (p ▸ f) b = f (p⁻¹ ▸ b) := 
begin hinduction p, refl end

@[hott]
def homotopy_eq_rinv {A B : Type _} {f g : A -> B} {H : f ~ g} :
  apd10 (eq_of_homotopy H) = H :=
@is_equiv.right_inv _ _ _ (eq_equiv_homotopy f g).to_is_equiv H  

@[hott]
def deq_of_homotopy3' {A C : Type _} {f₁ f₂ : A -> C} (p : f₁ = f₂) {B : A -> A -> Type _} 
  {D : Π (f : A -> C), Π (a₁ a₂ : A), B a₁ a₂ -> Type _} 
  {g₁ : Π (a₁ a₂ : A) (b : B a₁ a₂), D f₁ a₁ a₂ b} 
  {g₂ : Π (a₁ a₂ : A) (b : B a₁ a₂), D f₂ a₁ a₂ b} : 
  (Π (a₁ a₂ : A) (b : B a₁ a₂), g₁ a₁ a₂ b =[p; λ (f : A -> C), D f a₁ a₂ b] g₂ a₁ a₂ b) -> 
      g₁ =[p; λ (f : A -> C), Π (a₁ a₂ : A) (b : B a₁ a₂), D f a₁ a₂ b] g₂ :=
begin 
  hinduction p, intro hty, apply pathover_idp_of_eq, 
  exact eq_of_homotopy3 (λ (a₁ a₂ : A) (b : B a₁ a₂), eq_of_pathover_idp (hty a₁ a₂ b))  
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

/- The calculation rules for dependent if-then-else `dite` are missing in 
   [hott.init.logic]: Instances of the decision-clause may be not equal, and then the 
   eliminator `decidable.rec` does not work. This problem vanishes if the decision-clause 
   is a proposition. Also, equivalent decision-clauses leading to equal 
   then-else-branches are equal if-then-else statements. -/
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

@[hott]
def equiv_dite {c : Type _} [is_prop c] [H : decidable c] {c' : Type _} [is_prop c'] 
  [H' : decidable c'] {A : Type _} {t : c -> A} {e : ¬c -> A} {t' : c' -> A} 
  {e' : ¬c' -> A} : (c <-> c') -> (Π (Hc : c) (Hc' : c'), t Hc = t' Hc') ->
  (Π (Hnc : ¬c) (Hnc' : ¬c'), e Hnc = e' Hnc') -> dite c t e = dite c' t' e' :=
begin 
  intros equiv pos_eq neg_eq, fapply @decidable.rec c (λ H, dite c t e = dite c' t' e'),
  { intro Hc, fapply @decidable.rec c' (λ H', dite c t e = dite c' t' e'),
    { intro Hc', rwr dif_pos Hc, rwr dif_pos Hc', exact pos_eq Hc Hc' },
    { intros Hnc', hinduction Hnc' (equiv.1 Hc) },
    { exact H' } },
  { intro Hnc, fapply @decidable.rec c' (λ H', dite c t e = dite c' t' e'),
    { intro Hc', hinduction Hnc (equiv.2 Hc') },
    { intro Hnc', rwr dif_neg Hnc, rwr dif_neg Hnc', exact neg_eq Hnc Hnc' },
    { exact H' } },
  { exact H } 
end  

/- We need some equivalent descriptions of equalities of functions. -/
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
def fn2_ev_fn2_tr {A : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} (b₁ : B a₁) 
  (f : Π (a : A), B a -> Type _) : f a₁ b₁ = f a₂ (p ▸ b₁) :=
begin hinduction p, refl end

@[hott]
def fn2_ev_fn2_tr' {A C : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} (b₁ : B a₁) 
  (f : Π (a : A), B a -> C) : f a₁ b₁ = f a₂ (p ▸ b₁) :=
begin hinduction p, refl end

@[hott]
def fn3_ev_fn3_tr {A : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} (b₁ : B a₁) 
  {C : Π (a : A), B a -> Type _} (c₁ : C a₁ b₁) (f : Π (a : A) (b : B a), C a b -> Type _) : 
  f a₁ b₁ c₁ = f a₂ (p ▸ b₁) ((fn2_ev_fn2_tr p b₁ C) ▸[id] c₁) :=
begin hinduction p, refl end

def fn3_ev_fn3_tr' {A D : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} (b₁ : B a₁) 
  {C : Π (a : A), B a -> Type _} (c₁ : C a₁ b₁) (f : Π (a : A) (b : B a), C a b -> D) : 
  f a₁ b₁ c₁ = f a₂ (p ▸ b₁) ((fn2_ev_fn2_tr p b₁ C) ▸[id] c₁) :=
begin hinduction p, refl end

@[hott]
def fn_eq_tr_fn2 {A B : Type _} {a₁ a₂ : A} {f₁ f₂ : A -> B} (p : f₁ = f₂) 
  {C : B -> B -> Type _} {c₁ : C (f₁ a₁) (f₁ a₂)} : 
  p ▸ c₁ = ((ap10 p a₂) ▸[λ b : B, C (f₂ a₁) b] 
                           ((ap10 p a₁) ▸[λ b : B, C b (f₁ a₂)] c₁)) :=
begin hinduction p, refl end

@[hott]
def tr_tr_fn2_fn2_fn {A D E : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _}
  {b₁ : B a₁} {b₂ : B a₂} (q : b₁ =[p] b₂) {C : D -> E -> Type _} 
  {g : Π (a : A), B a -> D} {h : A -> E} (f : Π (a : A) (b : B a), C (g a b) (h a)) :
  f a₂ b₂ = ((ap h p) ▸[λ e : E, C (g a₂ b₂) e] ((apd011 g p q) ▸[λ d : D, C d (h a₁)] 
            f a₁ b₁)) :=
begin hinduction p, hinduction q, refl end

@[hott]
def tr_endo_eval_tr_tr {A : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} 
  (f : B a₁ -> B a₁) (b₁ : B a₁) : p ▸ (f b₁) = (p ▸ f) (p ▸ b₁) :=
begin hinduction p, exact idp end

@[hott]
def tr_endo_eval_tr_endo_tr {A : Type _} {a₁ a₂ : A} (p : a₁ = a₂) {B : A -> Type _} 
  (f : B a₁ -> B a₁) (b₂ : B a₂) : (p ▸ f) b₂ = p ▸ (f (p⁻¹ ▸ b₂)) :=
begin hinduction p, exact idp end

@[hott]
def fn_pathover_equiv_of_eq {A B C : Type _} (f : A -> C) (g : B -> C) (p : A = B) :
  f = g ∘ equiv.equiv_of_eq p -> f =[p; λ A : Type _, A -> C] g :=
begin 
  hinduction p, hsimp, intro q, apply pathover_idp_of_eq, 
  apply eq_of_homotopy, intro a, exact ap10 q a 
end  

@[hott]
def fn_pathover_equiv_of_eq' {A B C : Type _} (f : A -> B) (g : A -> C) (p : B = C) :
  g = equiv.equiv_of_eq p ∘ f -> f =[p; λ B : Type _, A -> B] g :=
begin 
  hinduction p, hsimp, intro q, apply pathover_idp_of_eq, 
  apply eq_of_homotopy, intro a, exact (ap10 q a)⁻¹ 
end  

end hott