import types.nat2

universes u v w
hott_theory

namespace hott
open hott.is_equiv hott.is_trunc hott.trunc hott.nat 

/- Some inequalities of natural numbers in the core are non-HoTT propositions, so procedures
   using them need to be rewritten.  -/
@[hott, hsimp] 
def list_nth_le {α : Type _} : Π (l : list α) (n), n < l.length → α
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := a
| (a :: l) (n+1) h := list_nth_le l n (le_of_succ_le_succ h)

@[hott]
def list_nth_le_eq {α : Type _} : Π {l : list α} {n : ℕ} (p p' : n < l.length),
  list_nth_le l n p = list_nth_le l n p' :=
assume l n p p', ap (list_nth_le l n) (is_prop.elim p p')

@[hott]
def list_nth_le_eq' {α : Type _} : Π {l : list α} {n m : ℕ} (p : n < l.length)
  (p' : m < l.length), n = m -> list_nth_le l n p = list_nth_le l m p' :=
begin intros l n m p p' q, hinduction q, exact list_nth_le_eq p p' end

/- Further facts on lists -/
@[hott, hsimp]
def list_map_size_eq {A B : Type _} (f : A -> B) (l : list A) : 
  list.length (list.map f l) = list.length l :=
begin hinduction l, refl, hsimp, rwr ih end  

@[hott]
def list_eq {A : Type _} {l₁ l₂ : list A} {a₁ a₂ : A} (ptl : l₁ = l₂) (phd : a₁ = a₂) :
  a₁ :: l₁ = a₂ :: l₂ := 
ap011 list.cons phd ptl

@[hott]
def list_length_append {A : Type _} (l₁ l₂ : list A) : 
  list.length (l₁ ++ l₂) = list.length l₁ + list.length l₂ :=
begin 
  hinduction l₁, hsimp, 
  change list.length (tl ++ l₂) + 1 = (list.length tl + 1) + list.length l₂, rwr ih,
  rwr nat.add_assoc, rwr nat.add_assoc, rwr nat.add_comm _ 1 
end

@[hott]
def list_append_el₁ {A : Type u} (l₁ l₂ : list A) (n : ℕ) (p : n < list.length l₁) :
  let q : n < list.length (l₁ ++ l₂) :=  
    nat.lt_of_lt_of_le (nat.lt_of_lt_of_le p (nat.le_add_right (list.length l₁) 
                    (list.length l₂))) (nat.le_of_eq (list_length_append l₁ l₂)⁻¹) in
  list_nth_le (l₁ ++ l₂) n q = list_nth_le l₁ n p :=
begin
  revert n p, hinduction l₁, 
    intros n p, hinduction nat.not_lt_zero n p,
    intro n, hinduction eq_zero_sum_eq_succ_pred n,  
      rwr val, intro p, exact idp,
      rwr val, intro p, hsimp, 
      let p' : (nat.pred n) < list.length tl := nat.le_of_succ_le_succ p, 
      apply square_diag_id (ih (nat.pred n) p'), 
      exact ap (list_nth_le _ _) (is_prop.elim _ _),
      exact ap (list_nth_le _ _) (is_prop.elim _ _)
end 

@[hott]
def list_append_el₂ {A : Type _} (l₁ l₂ : list A) (n : ℕ) (p : n < list.length l₂) :
  let q : list.length l₁ + n < list.length (l₁ ++ l₂) := 
    nat.lt_of_lt_of_le (nat.add_lt_add_left p (list.length l₁)) 
                                          (nat.le_of_eq (list_length_append l₁ l₂)⁻¹) in
  list_nth_le (l₁ ++ l₂) (list.length l₁ + n) q = list_nth_le l₂ n p :=
begin 
  hinduction l₁, 
    hsimp, apply list_nth_le_eq' _ _, exact nat.zero_add n, 
    hsimp, hsimp at ih, rwr <- ih, let q := nat.succ_add (list.length tl) n, 
    rwr apd011' (list_nth_le (hd :: (tl ++ l₂))) q, hsimp, rwr list_nth_le_eq
end 

/- Concatenating lists is associative. -/
@[hott]
def list_append_nil {A : Type _} : Π (l : list A), list.append l [] = l :=
  begin intro l, hinduction l, exact idp, exact ap (list.cons hd) ih end

@[hott]
def list_append_is_assoc {A : Type _} : Π (l₁ l₂ l₃ : list A), 
  list.append (list.append l₁ l₂) l₃ = list.append l₁ (list.append l₂ l₃)
| []       _  _  := idp
| _        [] _  := by rwr list_append_nil
| _        _  [] := by rwr list_append_nil; rwr list_append_nil
| (a₁::l₁) l₂ l₃  := begin change a₁::(list.append _ _) = a₁::(list.append _ _), 
                           rwr list_append_is_assoc end

/- Properties of reversing lists -/
@[hott]
def list_reverse_append {A : Type _} : Π (l₁ l₂ : list A),
  list.reverse_core l₁ l₂ = list.append (list.reverse l₁) l₂ :=
begin
  intro l₁, hinduction l₁, 
  { intro l₂, exact idp },
  { intro l₂, change list.reverse_core tl (hd :: l₂) = _, rwr ih (hd :: l₂), 
    change _ = list.append (list.reverse_core tl [hd]) _, rwr ih [hd],
    rwr list_append_is_assoc } 
end

end hott