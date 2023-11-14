import hott.types.nat.default

universes u u' v w
hott_theory

namespace hott

open hott.nat

namespace nat

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
def gt_list_tl : Π (a : ℕ) (hd : nat) (tl : list ℕ), 
  gt_list a (hd::tl) -> gt_list a tl :=
sorry

@[hott, instance]
def decidable_gt_list : Π (a : ℕ) (l : list ℕ), decidable (gt_list a l) :=
begin
  intros a l, hinduction l, 
    exact decidable.inl (gt_list.empty a), 
    hinduction decidable_lt hd a,
      hinduction ih, 
        exact decidable.inl (gt_list.next hd tl a_1 a_2),
        apply decidable.inr, intro gtl, exact a_2 (gt_list_tl _ _ _ gtl),
      apply decidable.inr, intro gtl, exact a_1 (gt_list_hd _ _ _ gtl)
end

#print decidable_gt_list

--#reduce ite (gt_list_nat 2 [0, 1]) 1 0

end nat

end hott