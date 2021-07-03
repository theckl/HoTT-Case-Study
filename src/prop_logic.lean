import hott.init hott.types.trunc hott.types.prod init2 prop_axioms

universes u v w
hott_theory

namespace hott
open is_trunc trunc equiv hott.is_equiv hott.prod 

/- [and], [or] and [iff] produce propositions from propositions. -/
@[hott]
protected def and (P Q : Prop) : Prop :=
  Prop.mk (P × Q) (prod.is_trunc_prod P Q -1)   

infix `and`:50 := hott.and 

@[hott]
protected def or (P Q : Prop) : Prop :=
  ∥P ⊎ Q∥ 

infix `or`:49 := hott.or 

@[hott]
def or_inl (P Q : Prop) : P -> P or Q :=
begin intro p, apply tr, exact sum.inl p end

@[hott]
def or_inr (P Q : Prop) : Q -> P or Q :=
begin intro q, apply tr, exact sum.inr q end

@[hott]
def or_symm {P Q : Prop} : P or Q -> Q or P :=
begin
  intro r, hinduction r, hinduction a with p q, 
  { apply tr, exact sum.inr p }, 
  { apply tr, exact sum.inl q }
end 

@[hott] 
def Not (P : trunctype.{u} -1) : Prop :=
  to_Prop (P -> False.{u})

/- Double negation -/
@[hott]
def not_not (P : Prop) : Not (Not P) <-> P :=
begin
  apply pair,
  { intro nnP, hinduction LEM P, --non-constructive
    { assumption },
    { have nP : ↥(Not P), by intro p; hinduction val p,
      hinduction nnP nP } },
  { intros p nP, hinduction nP p }
end  

/- De Morgan's Laws which are partially non-constructive. -/
@[hott]
def not_and (P Q : trunctype.{u} -1) : Not (P and Q) <-> (Not P) or (Not Q) :=
begin
  apply pair,
  { intro na, apply tr, hinduction LEM P, --this is non-constructive
    { hinduction LEM Q, 
      { hinduction na ⟨val, val_1⟩ },
      { exact sum.inr (λ q, empty.elim (val_1 q)) } }, 
    { exact sum.inl (λ p, empty.elim (val p)) } },
  { intro norn, intro PQ, hinduction norn, hinduction a, 
    { exact val PQ.1 }, 
    { exact val PQ.2 } }
end 

@[hott]
def not_or (P Q : trunctype.{u} -1) : Not (P or Q) <-> (Not P) and (Not Q) :=
begin
  apply pair,
  { intro no, 
    have nP : ↥(Not P), by intro p; hinduction no (or_inl P Q p),
    have nQ : ↥(Not Q), by intro q; hinduction no (or_inr P Q q),
    exact ⟨nP, nQ⟩ },
  { intros nPnQ PorQ, hinduction PorQ, hinduction a with p q, 
    { exact nPnQ.1 p },
    { exact nPnQ.2 q } }
end  

/- Contraposition -/
@[hott]
def contrapos (P Q : trunctype.{u} -1) : (P -> Q) <-> (Not Q -> Not P) :=
begin
  apply pair,
  { intros imp nQ p, exact nQ (imp p) },
  { intros nimp p, hinduction LEM Q, 
    { assumption },
    { have nQ : ↥(Not Q), by intro q; hinduction val q, 
      hinduction nimp nQ p } }
end  
  
/- Negation of implication -/
@[hott]
def neg_imp (P Q : Prop) : Not (to_Prop (P -> Q)) <-> (P and Not Q) :=
begin 
  apply pair, 
  { apply (contrapos _ _).2, 
    rwr prop_iff_eq (not_and _ _).1 (not_and _ _).2, 
    rwr prop_iff_eq (not_not Q).1 (not_not Q).2,
    rwr prop_iff_eq (not_not _).1 (not_not _).2, 
    intro nPorQ, hinduction nPorQ, hinduction a with nP q, 
    { intro p, hinduction nP p },
    { exact λ p, q } },
  { intros PnQ PQ, exact PnQ.2 (PQ PnQ.1) }
end 

/- A useful rule to deal with negated statements. -/
@[hott]
def Not_eq_False {P : Prop} : Not P -> P = False :=
begin  
  intro np, apply prop_iff_eq, 
  { intro p, hinduction np p },
  { intro f, induction f }
end  

/- The universe lift of propositions commutes with logical operators. -/
@[hott]
def prop_ulift_or (P Q : Prop) : 
  prop_ulift (P or Q) = (prop_ulift P or prop_ulift Q) :=
begin 
  apply prop_iff_eq, 
  { intro lift_or, hinduction lift_or with tr_PorQ, hinduction tr_PorQ with PorQ,
    hinduction PorQ with p q,
    { apply tr, exact sum.inl (ulift.up p) },
    { apply tr, exact sum.inr (ulift.up q) } },
  { intro or_lift, hinduction or_lift with sum_lift, hinduction sum_lift with p q, 
    { hinduction p with p', apply ulift.up, apply tr, exact sum.inl p' },
    { hinduction q with q', apply ulift.up, apply tr, exact sum.inr q' } }
end    

@[hott]
def ulift_False : prop_ulift False = False :=
begin 
  apply prop_iff_eq, 
  { intro f, hinduction ulift_equiv.to_fun f },
  { intro f, hinduction f } 
end

/- We need some statements from first-order logic. -/
@[hott]
def not_all {A : Type _} (P : A -> Prop) : 
  Not (to_Prop (∀ a : A, P a)) <-> ∥Σ a : A, Not (P a)∥ :=
begin
  apply pair,  
  { apply (contrapos _ _).2, intros nenP, 
    apply (not_not (to_Prop (Π (a : A), P a))).2, intro a, 
    hinduction LEM (P a), 
    { assumption },
    { have nPa : ↥(Not (P a)), by intro Pa; hinduction val Pa,
      hinduction nenP (tr ⟨a, nPa⟩) } },
  { intros enP aP, hinduction enP, exact a.2 (aP a.1) }
end  

end hott