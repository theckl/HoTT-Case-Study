import sets.basic categories.models

universes v v' u u' w 
hott_theory

namespace hott

open subset signature term formula hott.set hott.is_trunc

namespace ring

/- At the moment, we only need commutative rings with one. -/

@[hott]
protected def sign : fo_signature :=
begin
  fapply fo_signature.mk,
  exact dec_nat, -- let's see whether this is easier than introducing strings
  exact dec_fin_Set 1, --one sort
  exact dec_fin_Set 5, --five operations : add, mult, zero, one, neg
  exact dec_fin_map_of_list [2, 2, 0, 0, 1],   --arities of operations
  exact λ o a, ⟨0, nat.zero_lt_succ 0⟩, --sources and targets of operations can only                                     
  exact λ o, ⟨0, nat.zero_lt_succ 0⟩,   --have one sort
  exact dec_fin_Set 0, --no extra relations : the laws for addition and multiplication are
                   --                     axioms of the theory of rings 
  intro f, hinduction nat.not_lt_zero f.1 f.2, --no arities of relations needed 
  exact λ r a, ⟨0, nat.zero_lt_succ 0⟩, --no sources of relations exist 
  exact dec_fin_Set 0,  --no infinite dis-/conjunctions needed
  intro ind, hinduction nat.not_lt_zero ind.1 ind.2
end

@[hott, instance]
def ring_sorts_is_prop : is_prop ↥(ring.sign.sorts) :=
  by change is_prop (fin_Set 1); apply_instance

@[hott]
protected def sort : ring.sign.sorts := ⟨0, nat.zero_lt_succ 0⟩

@[hott, reducible]
def xv_ (n : ℕ) : to_Set (var ring.sign.labels ring.sign.sorts) := var.mk n ring.sort

@[hott, reducible]
def x_ (n : ℕ) : term ring.sign := 
  term.mk ring.sort (term_of_sort.var ring.sort (xv_ n) idp)

notation `x₀` := x_ 0
notation `x₁` := x_ 1
notation `x₂` := x_ 2

@[hott, reducible]
def op_add : (fin_Set 2 -> term_of_sort ring.sort) -> term_of_sort ring.sort :=
begin
  intro term_op, fapply term_of_sort.op, 
  exact ⟨0, nat.zero_lt_succ 4⟩, exact is_prop.elim _ _,
  intro oa, rwr is_prop.elim (ring.sign.ops_source ⟨0, nat.zero_lt_succ 4⟩ oa) ring.sort,
  have p : ring.sign.ops_arity ⟨0, nat.zero_lt_succ 4⟩ = 2, by refl,  
  rwr p at oa, exact term_op oa
end

@[hott, reducible]
def add : term ring.sign -> term ring.sign -> term ring.sign :=
begin
  intros t₁ t₂, fapply term.mk, exact ring.sort,
  have p₁ : t₁.sort = ring.sort, from is_prop.elim _ _, 
  have p₂ : t₂.sort = ring.sort, from is_prop.elim _ _,
  exact op_add (fin_map_of_list [p₁ ▸ t₁.expr, p₂ ▸ t₂.expr]) 
end

@[hott]
def add_FV : Π (t₁ t₂ : term ring.sign), free_vars_of_term (add t₁ t₂) =
  free_vars_of_term t₁ ∪ free_vars_of_term t₂ :=
begin
  intros t₁ t₂, hinduction t₁ with sort₁ expr₁, hinduction t₂ with sort₂ expr₂, 
  hsimp only [free_vars_of_term], 
  have p : (ring.sign.ops_arity ⟨0, nat.zero_lt_succ 4⟩) = 2, from rfl, 
  apply inc_inc_dec_eq,
  { apply inc_dec_fin_iUnion_inc _ _, intro m, 
    hinduction nat.eq_sum_lt_of_le (nat.zero_le m.1), 
    { apply inc_l_dec_union, apply eq_dec_subset, 
      fapply apd011 (@term_of_sort.rec _ _ _ _ : Π s, term_of_sort s -> free_vars ring.sign), 
      exact is_prop.elim _ _, rwr idp_tr, hinduction m, rwr <- fin_map_of_list_el, 
      hsimp at val, rwr @list_nth_le_eq' _ [is_prop.elim sort₁ ring.sort ▸ expr₁, 
                      is_prop.elim sort₂ ring.sort ▸ expr₂] fst 0 snd (val⁻¹ ▸ snd) val⁻¹,
      hsimp only [list_nth_le], apply pathover_of_tr_eq, apply (λ p, p ⬝ (idp_tr expr₁)), 
      rwr <- con_tr, rwr <- con_tr, apply ap (λ p, p ▸ expr₁), exact is_prop.elim _ _ },
    { apply inc_r_dec_union, apply eq_dec_subset, 
      fapply apd011 (@term_of_sort.rec _ _ _ _ : Π s, term_of_sort s -> free_vars ring.sign), 
      exact is_prop.elim _ _, rwr idp_tr, hinduction m, rwr <- fin_map_of_list_el, 
      hsimp at val, hinduction nat.eq_sum_lt_of_le val,
      { rwr @list_nth_le_eq' _ [is_prop.elim sort₁ ring.sort ▸ expr₁, 
          is_prop.elim sort₂ ring.sort ▸ expr₂] fst (nat.succ 0) snd 
                                                                 (val_1⁻¹ ▸ snd) val_1⁻¹,
        hsimp only [list_nth_le], apply pathover_of_tr_eq, apply (λ p, p ⬝ (idp_tr expr₂)), 
        rwr <- con_tr, rwr <- con_tr, apply ap (λ p, p ▸ expr₂), exact is_prop.elim _ _ },
      { rwr p at snd, hinduction nat.lt_irrefl 2 (nat.lt_of_le_of_lt val_1 snd) } } }, 
  { apply inc_inc_dec_union_inc, 
    { apply inc_comp_dec_fin_iUnion, fapply dpair, exact ⟨0, p⁻¹ ▸ nat.zero_lt_succ 1⟩, 
      rwr idp_tr, rwr <- fin_map_of_list_el, hsimp only [list_nth_le], apply eq_dec_subset,
      fapply apd011 (@term_of_sort.rec _ _ _ _ : Π s, term_of_sort s -> free_vars ring.sign),
      exact is_prop.elim _ _, apply pathover_of_tr_eq, rwr <- con_tr },
    { apply inc_comp_dec_fin_iUnion, fapply dpair, exact ⟨nat.succ 0, p⁻¹ ▸ nat.le_refl 2⟩,
      rwr idp_tr, rwr <- fin_map_of_list_el, hsimp only [list_nth_le], apply eq_dec_subset,
      fapply apd011 (@term_of_sort.rec _ _ _ _ : Π s, term_of_sort s -> free_vars ring.sign),
      exact is_prop.elim _ _, apply pathover_of_tr_eq, rwr <- con_tr } }
end

@[hott, reducible]
def FV_add_assoc : dec_Subset (to_Set (var ring.sign.labels ring.sign.sorts)) :=
  free_vars_of_term (add (add x₀ x₁) x₂) ∪ 
                               free_vars_of_term (add x₀ (add x₁ x₂))

@[hott]
def FV_add_assoc_eq : FV_add_assoc = (dec_sset_of_list [xv_ 0, xv_ 1, xv_ 2]) :=
begin
  have p : free_vars_of_term (add (add x₀ x₁) x₂) = (dec_sset_of_list [xv_ 0, xv_ 1, xv_ 2]), from 
  begin
    rwr add_FV, rwr add_FV, 
    change singleton_dec_sset (xv_ 0) ∪ singleton_dec_sset (xv_ 1) ∪ 
                                                singleton_dec_sset (xv_ 2) = _,
    rwr singleton_dec_sset_of_list, rwr singleton_dec_sset_of_list, 
    rwr singleton_dec_sset_of_list, rwr union_dec_sset_of_list, rwr union_dec_sset_of_list
  end,
  have q : free_vars_of_term (add x₀ (add x₁ x₂)) = (dec_sset_of_list [xv_ 0, xv_ 1, xv_ 2]), from 
  begin
    rwr add_FV, rwr add_FV, 
    change singleton_dec_sset (xv_ 0) ∪ (singleton_dec_sset (xv_ 1) ∪ 
                                                singleton_dec_sset (xv_ 2)) = _,
    rwr singleton_dec_sset_of_list, rwr singleton_dec_sset_of_list, 
    rwr singleton_dec_sset_of_list, rwr union_dec_sset_of_list, rwr union_dec_sset_of_list
  end,                               
  change _ ∪ _ = _, rwr p, rwr q, apply dec_sset_eq_of_sset_eq, rwr dec_union_is_union, 
  exact union.idempot
end                                           

@[hott]
def add_assoc : formula FV_add_assoc :=
  formula.eq_terms (add (add x₀ x₁) x₂) (add x₀ (add x₁ x₂)) idp

@[hott, instance]
def add_assoc_is_atom : formula.is_atomic add_assoc :=
  begin apply is_atomic.mk, hsimp, exact true.intro end

@[hott, reducible]
def add_assoc_seq : sequent ring.sign :=
begin
  fapply sequent.mk,
  { exact form_FV.mk (no_FV ring.sign) formula.T },
  { exact form_FV.mk FV_add_assoc add_assoc },
  { exact context.mk FV_add_assoc },
  { hsimp, apply inc_to_dec_inc, rwr dec_union_is_union, rwr empty_dec_sset_empty_sset,
    rwr empty_union, exact subset_refl _ }
end

@[hott]
protected def theory : fo_theory ring.sign :=
  sset_of_list [add_assoc_seq]

@[hott, instance]
def ring_theory_is_alg : theory.is_algebraic ring.theory :=
begin
  fapply theory.is_algebraic.mk, 
  { exact idp },
  { intros seq inc, sorry },
  { sorry },
  { sorry }
end

end ring

end hott