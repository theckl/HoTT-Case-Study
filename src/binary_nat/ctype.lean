import hott.types.nat.default

universes u u' v w
hott_theory

namespace hott

open hott.nat

namespace nat

/- Tools to construct strictly increasing lists of natural numbers.-/
@[hott]
inductive gt_list (a : ℕ) : (list ℕ) -> Type
| empty : gt_list []
| next : Π (hd : nat) (tl : list ℕ), (a > hd) -> (gt_list tl) -> (gt_list (hd::tl))  

@[hott]
def gt_list_hd {a : ℕ} {l : list ℕ} : 
  gt_list a l -> if' (l.length = 0) then (0 ≤ a) else (a > l.head) :=
begin
  intro gtl, hinduction gtl, 
    exact nat.zero_le a,
    exact a_1
end

@[hott]
def gt_list_hd' {a : ℕ} {hd : ℕ} {tl : list ℕ} : 
  gt_list a (hd::tl) -> a > hd :=
assume gtl, gt_list_hd gtl

@[hott]
def gt_list_tl {a : ℕ} {l : list ℕ} : 
  gt_list a l -> if' (l.length = 0) then (0 ≤ a) else gt_list a l.tail :=
begin
  intro gtl, hinduction gtl, 
    exact nat.zero_le a,
    exact a_2
end

@[hott]
def gt_list_tl' {a : ℕ} {hd : nat} {tl : list ℕ} : 
  gt_list a (hd::tl) -> gt_list a tl :=
assume gtl, gt_list_tl gtl

@[hott, instance]
def decidable_gt_list : Π (a : ℕ) (l : list ℕ), decidable (gt_list a l) :=
begin
  intros a l, hinduction l, 
    exact decidable.inl (gt_list.empty a), 
    hinduction decidable_lt hd a,
      hinduction ih, 
        exact decidable.inl (gt_list.next hd tl a_1 a_2),
        apply decidable.inr, intro gtl, exact a_2 (gt_list_tl' gtl),
      apply decidable.inr, intro gtl, exact a_1 (gt_list_hd' gtl)
end

end nat

/- Direction sets on which cubes are built are implemented as strictly increasing lists of
   natural numbers. -/
@[hott]
inductive is_ord_set : list ℕ -> Type
| empty : is_ord_set []
| next : Π (n : ℕ) (tl : list ℕ), is_ord_set tl -> nat.gt_list n tl -> is_ord_set (n::tl) 

@[hott]
structure directions :=
  (dir : list ℕ)
  (ord : is_ord_set dir)

namespace partial_order

@[hott, class] 
structure partial_order (A : Type _) extends has_le A :=
  (le_refl : Πa, le a a)
  (le_trans : Πa b c, le a b → le b c → le a c)
  (le_antisymm : Πa b, le a b → le b a → a = b)

@[hott]
def is_po_unit {A : Type _} [partial_order A] (one : A) := 
  Π a : A, a ≤ one 

@[hott]
def po_unit_is_unique {A : Type _} [po : partial_order A] : 
  Π a a' : A, is_po_unit a -> is_po_unit a' -> a = a' :=
λ a a' pou pou', partial_order.le_antisymm _ _ (pou' a) (pou a')   

end partial_order

end hott