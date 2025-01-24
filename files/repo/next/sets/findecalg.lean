import sets.dec_alg

--subset sets.finite sets.axioms hott.types.prod hott.types.nat.sub

universes u v w
hott_theory

namespace hott
open hott.set subset prod trunc is_trunc sum

namespace subset

/- We prove several facts on finiteness of decidable subsets under algebraic operations.
   Since some of them rely on the fact that a decidable subset of a finite decidable 
   subset is finite, decidability is essential here: The finiteness of subsets of finite
   subsets is equivalent to LEM, see Andrej Bauer's article on constructivism. 
   
   We start with an inductive step : Taking away one element decreases the size of a set 
   by 1. -/
@[hott]
def dec_sset_minus_el_bij {C : Set} [H : decidable_eq C] {A : dec_Subset C} {n : ℕ} 
  (f : bijection (fin_Set (n+1)) (dec_pred_Set A)) : bijection (fin_Set n) 
     (dec_pred_Set (dec_setminus A (singleton_dec_sset (f ⟨n, nat.le_refl (n+1)⟩).1))) :=
begin
  let fin_n : ↥(fin_Set (n+1)) := ⟨n, nat.le_refl (n+1)⟩,
  have Hm : Π m : fin_Set n, (f (fin_Set_lift (nat.le_succ n) m)).1 ≠ (f fin_n).1, from 
  begin 
    intros m eq1,  
    have eq : fin_Set_lift (nat.le_succ n) m = fin_n, from 
      is_set_bijective.inj f _ _ (dec_pred_Set_eq eq1),
    exact nat.lt_irrefl n (nat.lt_of_le_of_lt (nat.le_of_eq (ap sigma.fst eq)⁻¹) m.2)
  end, 
  have Hm' : Π m : fin_Set n, H (f (fin_Set_lift (nat.le_succ n) m)).1 (f fin_n).1 = 
                                                              decidable.inr (Hm m), from
  begin intro m, hinduction H (f (fin_Set_lift (nat.le_succ n) m)).1 (f fin_n).1,
    hinduction Hm m a, apply ap decidable.inr, exact is_prop.elim _ _ 
  end,
  let g := inv_bijection_of f,
  fapply bijection.mk,
  { intro m, fapply sigma.mk, 
    { exact (f (fin_Set_lift (nat.le_succ n) m)).1 },
    { change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _,
      let a_el := (f (fin_Set_lift (nat.le_succ n) m)).2, rwr a_el, hsimp,
      change @Two.rec (λ t : Two, Two) Two.one Two.zero 
                      (@decidable.rec ((f (fin_Set_lift (nat.le_succ n) m)).1 = 
                                                     (f fin_n).1) (λ p, Two) _ _ _) = _, 
      rwr Hm' m } },
  { fapply is_set_bijective.mk,
    { intros m m' p, 
      have q : f (fin_Set_lift (nat.le_succ n) m) = f (fin_Set_lift (nat.le_succ n) m'), from 
        dec_pred_Set_eq (ap sigma.fst p),
      apply fin_Set_eq, exact ap sigma.fst (is_set_bijective.inj f _ _ q) },
    { intro c_el, apply tr, fapply fiber.mk,
      { fapply sigma.mk,
        { exact (g ⟨c_el.1, dec_setminus_inc _ _ c_el.1 c_el.2⟩).1 },
        { let c_el' : ↥(dec_pred_Set A) := ⟨c_el.1, dec_setminus_inc _ _ c_el.1 c_el.2⟩,
          have nq : c_el' ≠ f fin_n, by 
            intro p; hinduction dec_setminus_single_neq (f fin_n).2 c_el'.1 c_el.2 
                                                                     (ap sigma.fst p),
          have q : f (g (c_el')) = c_el', by rwr inv_bij_r_inv,
          rwr <- q at nq, 
          have r : (g (c_el')).1 ≠ n, by 
            intro eq; change _ = fin_n.1 at eq; hinduction nq (ap f (fin_Set_eq eq)),
          exact nat.lt_of_le_neq (nat.le_of_succ_le_succ (g (c_el')).2) r } },
      { apply dec_pred_Set_eq, hsimp, 
        change (f (fin_Set_lift _ (fin_Set_desc _ _))).1 = _, rwr fin_Set_lift_desc,
        rwr inv_bij_r_inv } } }
end

/- We prove the finiteness of the union of two finite sets in two steps: First, we prove
   it when the two sets are disjoint. To simplify the calculations, we split up the 
   construction of the bijection to `fin_Set` according to the truth table of element 
   inclusions. -/
@[hott]
def fin_disj_union_map_0_0 {C : Set.{u}} {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB)) 
  (disj : A ∩ B = empty_dec_Subset C) {c : C} (el : (A ∪ B) c = Two.one) 
  (pa : A c = Two.zero) (pb : B c = Two.zero) :
  fin_Set (nA + nB) :=
begin
  change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at el, 
  rwr pa at el, rwr pb at el, hinduction encode_Two _ _ el
end

@[hott]
def fin_disj_union_map_0_1 {C : Set.{u}} {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB))
  (disj : A ∩ B = empty_dec_Subset C) {c : C} (el : (A ∪ B) c = Two.one) 
  (pa : A c = Two.zero) (pb : B c = Two.one) :
  fin_Set (nA + nB) :=
begin
  fapply sigma.mk, exact nA + (fin_bij_B ⟨c,pb⟩).1, 
  apply nat.add_lt_add_left, exact (fin_bij_B ⟨c, pb⟩).2
end

@[hott]
def fin_disj_union_map_1_0 {C : Set.{u}}  {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB))
  (disj : A ∩ B = empty_dec_Subset C) {c : C} (el : (A ∪ B) c = Two.one) 
  (pa : A c = Two.one) (pb : B c = Two.zero) :
  fin_Set (nA + nB) :=
begin
  fapply sigma.mk, exact (fin_bij_A ⟨c,pa⟩).1, 
  exact nat.lt_of_lt_of_le (fin_bij_A ⟨c, pa⟩).2 (nat.le_add_right _ _)
end

@[hott]
def fin_disj_union_map_1_1 {C : Set.{u}} {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB))
  (disj : A ∩ B = empty_dec_Subset C) {c : C} (el : (A ∪ B) c = Two.one) 
  (pa : A c = Two.one) (pb : B c = Two.one) :
  fin_Set (nA + nB) :=
begin
  have p : (A ∩ B) c = Two.zero, from ap10 disj c, 
  change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at p, 
  rwr pa at p, rwr pb at p, hinduction encode_Two _ _ p
end

@[hott, hsimp]
def fin_disj_union_map {C : Set.{u}} {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB)) 
  (disj : A ∩ B = empty_dec_Subset C) : dec_pred_Set (A ∪ B) -> fin_Set (nA + nB) :=
begin
  intro c_el, hinduction c_el with c el,
  all_goals { hinduction A c with pa }, all_goals { hinduction B c with pb }, 
  exact fin_disj_union_map_0_0 fin_bij_A fin_bij_B disj el pa pb,
  exact fin_disj_union_map_0_1 fin_bij_A fin_bij_B disj el pa pb,
  exact fin_disj_union_map_1_0 fin_bij_A fin_bij_B disj el pa pb,
  exact fin_disj_union_map_1_1 fin_bij_A fin_bij_B disj el pa pb 
end

@[hott]
def fin_disj_union_map_0_1_eq {C : Set.{u}} {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB)) 
  (disj : A ∩ B = empty_dec_Subset C) {c : C} (el : (A ∪ B) c = Two.one) 
  (pa : A c = Two.zero) (pb : B c = Two.one) :
  fin_disj_union_map fin_bij_A fin_bij_B disj ⟨c, el⟩ = 
      ⟨nA + (fin_bij_B ⟨c,pb⟩).1,
            nat.add_lt_add_left (fin_bij_B ⟨c,pb⟩).2 nA⟩ :=
begin
  hsimp, 
  have qa : idpath (A c) =[pa] pa, by apply pathover_of_tr_eq; exact is_prop.elim _ _,
  rwr @apd011 _ (fin_Set (nA + nB)) _ (A c) Two.zero 
             (idpath (A c)) pa (@Two.rec (λ t, (A c = t) -> fin_Set _) _ _) pa qa,
  hsimp,
  have qb : idpath (B c) =[pb] pb, by apply pathover_of_tr_eq; exact is_prop.elim _ _,
  rwr @apd011 _ (fin_Set (nA + nB)) _ (B c) Two.one 
             (idpath (B c)) pb (@Two.rec (λ t, (B c = t) -> fin_Set _) _ _) pb qb
end

@[hott]
def fin_disj_union_map_1_0_eq {C : Set} {A B : dec_Subset C} {nA nB : ℕ}
  (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB)) 
  (disj : A ∩ B = empty_dec_Subset C) {c : C} (el : (A ∪ B) c = Two.one) 
  (pa : A c = Two.one) (pb : B c = Two.zero) :
  fin_disj_union_map fin_bij_A fin_bij_B disj ⟨c, el⟩ = ⟨(fin_bij_A ⟨c, pa⟩).1,
          nat.lt_of_lt_of_le (fin_bij_A ⟨c, pa⟩).2 (nat.le_add_right _ _)⟩ :=
begin
  hsimp, 
  have qa : idpath (A c) =[pa] pa, by apply pathover_of_tr_eq; exact is_prop.elim _ _,
  rwr @apd011 _ (fin_Set (nA + nB)) _ (A c) Two.one 
             (idpath (A c)) pa (@Two.rec (λ t, (A c = t) -> fin_Set _) _ _) pa qa,
  hsimp,
  have qb : idpath (B c) =[pb] pb, by apply pathover_of_tr_eq; exact is_prop.elim _ _,
  rwr @apd011 _ (fin_Set (nA + nB)) _ (B c) Two.zero 
             (idpath (B c)) pb (@Two.rec (λ t, (B c = t) -> fin_Set _) _ _) pb qb
end

@[hott]
def fin_disj_union_map_inv {C : Set} [HC : decidable_eq C] {A B : dec_Subset C} 
  {nA nB : ℕ} (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB)) 
  (disj : A ∩ B = empty_dec_Subset C) : fin_Set (nA + nB) -> dec_pred_Set (A ∪ B) :=
begin 
  intro m,
  fapply @sum.rec _ _ (λ tot_sum, dec_pred_Set (A ∪ B)) _ _ (nat.lt_sum_ge m.1 nA),
  { intro val,
    fapply sigma.mk, exact (inv_bijection_of fin_bij_A ⟨m.1, val⟩).1,
    apply union_dec_sset_l _, exact (inv_bijection_of fin_bij_A ⟨m.1, val⟩).2 },
  { intro val, let val' := nat.sub_lt_of_lt_add m.2 val,
    fapply sigma.mk, 
      exact (inv_bijection_of fin_bij_B ⟨m.1 - nA, val'⟩).1,
      apply union_dec_sset_r _, 
      exact (inv_bijection_of fin_bij_B ⟨m.1 - nA, val'⟩).2 }
end

@[hott]
def fin_disj_union_map_linv {C : Set} [HC : decidable_eq C] {A B : dec_Subset C}
  {nA nB : ℕ} (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB)) 
  (disj : A ∩ B = empty_dec_Subset C) : Π c_el : dec_pred_Set (A ∪ B),
  fin_disj_union_map_inv fin_bij_A fin_bij_B disj 
                          (fin_disj_union_map fin_bij_A fin_bij_B disj c_el) = c_el :=
begin 
  intro c_el, hinduction c_el with c el,
  let m := fin_disj_union_map fin_bij_A fin_bij_B disj ⟨c, el⟩,
  hinduction A c with pa, all_goals { hinduction B c with pb }, 
  { change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at el, 
    rwr pa at el, rwr pb at el, hinduction encode_Two _ _ el },
  { change @sum.rec _ _ (λ tot_sum, dec_pred_Set (A ∪ B)) _ _ _ = _,
    hinduction nat.lt_sum_ge m.1 nA,
    { have p : (fin_disj_union_map fin_bij_A fin_bij_B disj ⟨c, el⟩).1 ≥ nA, by 
        rwr fin_disj_union_map_0_1_eq _ _ disj el pa pb; exact nat.le_add_right _ _,
      hinduction nat.not_succ_le_self (nat.lt_of_lt_of_le val p) },
    { change sigma.mk _ _ = _, fapply sigma.sigma_eq,
      { change ((inv_bijection_of fin_bij_B) _).1 = c,
        have pBm : fin_bij_B ⟨c,pb⟩ = 
               ⟨(fin_disj_union_map _ _ disj ⟨c, el⟩).1 - nA,
                                                      nat.sub_lt_of_lt_add m.2 val⟩, from 
        begin 
          fapply sigma.sigma_eq, 
          { change _ = (fin_disj_union_map _ _ disj ⟨c, el⟩).1 - nA, 
            rwr fin_disj_union_map_0_1_eq _ _ disj el pa pb, change _ = _ + _ - _, 
            rwr nat.add_sub_cancel_left' }, 
          { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
        end,
        rwr <- pBm, rwr inv_bij_l_inv },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } } },
  { change @sum.rec _ _ (λ tot_sum, dec_pred_Set (A ∪ B)) _ _ _ = _,
    hinduction nat.lt_sum_ge m.1 nA,
    { change sigma.mk _ _ = _, fapply sigma.sigma_eq,
      { change ((inv_bijection_of fin_bij_A) _).1 = c,
        have pAm : fin_bij_A ⟨c,pa⟩ = 
                     ⟨(fin_disj_union_map _ _ disj ⟨c, el⟩).1, val⟩, from 
        begin
          fapply sigma.sigma_eq, 
          { change _ = (fin_disj_union_map _ _ disj ⟨c, el⟩).1, 
            rwr fin_disj_union_map_1_0_eq _ _ disj el pa pb },
          { apply pathover_of_tr_eq, exact is_prop.elim _ _ }
        end,
        rwr <- pAm, rwr inv_bij_l_inv },
      { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },  
    { have p : (fin_disj_union_map _ _ disj ⟨c, el⟩).1 < nA, by 
        rwr fin_disj_union_map_1_0_eq _ _ disj el pa pb; exact (fin_bij_A ⟨c, pa⟩).2,
      hinduction nat.not_succ_le_self (nat.lt_of_lt_of_le p val) } },
  { have p : (A ∩ B) c = Two.zero, from ap10 disj c, 
    change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at p, 
    rwr pa at p, rwr pb at p, hinduction encode_Two _ _ p }
end

@[hott]
def fin_disj_union_map_rinv {C : Set} [HC : decidable_eq C] {A B : dec_Subset C}
  {nA nB : ℕ} (fin_bij_A : bijection (dec_pred_Set A) (fin_Set nA)) 
  (fin_bij_B : bijection (dec_pred_Set B) (fin_Set nB))
  (disj : A ∩ B = empty_dec_Subset C) : Π m : fin_Set (nA + nB),
  fin_disj_union_map fin_bij_A fin_bij_B disj (fin_disj_union_map_inv fin_bij_A fin_bij_B disj m) = m :=
begin 
  intro m, hinduction m with m pAB, hinduction nat.lt_sum_ge m nA,
  { change fin_disj_union_map _ _ _ 
                          (@sum.rec _ _ (λ tot_sum, dec_pred_Set (A ∪ B)) _ _ _) = _,
    let c_el := (inv_bijection_of (fin_bij_A)) ⟨m, val⟩,
    rwr _h, change fin_disj_union_map _ _ _ ⟨c_el.1, _⟩ = _,
    have pa : A c_el.1 = Two.one, from c_el.2,
    have qa : pa = c_el.2, from is_prop.elim _ _,
    have pb : B c_el.1 = Two.zero, from 
    begin 
      have p : (A ∩ B) c_el.1 = Two.zero, from ap10 disj c_el.1, 
      change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at p, 
      rwr pa at p, hinduction (B c_el.1) with pb, 
      refl, rwr pb at p, hinduction encode_Two _ _ p
    end,
    rwr fin_disj_union_map_1_0_eq _ _ _ _ pa pb, fapply sigma.sigma_eq,
    { hsimp, rwr qa, rwr sigma.eta, rwr inv_bij_r_inv fin_bij_A ⟨m, val⟩ },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } },
  { change fin_disj_union_map _ _ _ 
                          (@sum.rec _ _ (λ tot_sum, dec_pred_Set (A ∪ B)) _ _ _) = _,
    let val' := nat.sub_lt_of_lt_add pAB val,
    let c_el := (inv_bijection_of fin_bij_B) ⟨m - nA, val'⟩,
    rwr _h, change fin_disj_union_map _ _ _ ⟨c_el.1, _⟩ = _,
    have pb : B c_el.1 = Two.one, from c_el.2,
    have qb : pb = c_el.2, from is_prop.elim _ _,
    have pa : A c_el.1 = Two.zero, from 
    begin 
      have p : (A ∩ B) c_el.1 = Two.zero, from ap10 disj c_el.1, 
      change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at p, 
      rwr pb at p, hinduction (A c_el.1) with pa, 
      refl, rwr pa at p, hinduction encode_Two _ _ p
    end,
    rwr fin_disj_union_map_0_1_eq _ _ _ _ pa pb, fapply sigma.sigma_eq,
    { hsimp, rwr qb, rwr sigma.eta, 
      rwr inv_bij_r_inv fin_bij_B ⟨m - nA, val'⟩,
      hsimp, change _ + (_ - _) = _, rwr <- nat.add_sub_assoc val, 
      rwr nat.add_sub_cancel_left' },
    { apply pathover_of_tr_eq, exact is_prop.elim _ _ } }
end

@[hott]
def fin_disj_union_fin {C : Set} [HC : decidable_eq C] {A B : dec_Subset C} :
  is_finite_dec_sset A -> is_finite_dec_sset B -> (A ∩ B = empty_dec_Subset C) ->
  is_finite_dec_sset (A ∪ B) := 
begin
  intros fin_A fin_B disj, 
  hinduction fin_A with fin_A, hinduction fin_A with nbA, 
  hinduction nbA with nA ex_bij_A, hinduction ex_bij_A with bij_A,
  hinduction fin_B with fin_B, hinduction fin_B with nbB, 
  hinduction nbB with nB ex_bij_B, hinduction ex_bij_B with bij_B,
  apply is_finite_dec_sset.mk, apply is_finite.mk, 
  fapply sigma.mk, exact nA + nB, apply tr,
  fapply has_inverse_to_bijection,  
  { exact fin_disj_union_map bij_A bij_B disj },
  { exact fin_disj_union_map_inv bij_A bij_B disj },
  { fapply is_set_inverse_of.mk, 
    { exact fin_disj_union_map_rinv bij_A bij_B disj },
    { exact fin_disj_union_map_linv bij_A bij_B disj } }
end 

/- To prove the finiteness of unions (and intersections) in general, we need that a 
   decidable subset of a finite decidable subset is finite. In the inductive step, we use
   that a decidable subset is finite if this subset minus an element is finite. -/
@[hott]
def fin_setminus_fin {C : Set} [HC : decidable_eq C] {A : dec_Subset C} (c : C) : 
  is_finite_dec_sset (dec_setminus A (singleton_dec_sset c)) -> is_finite_dec_sset A :=
begin 
  intro fin_dec_sm, hinduction A c with p,
  { have q : dec_setminus A (singleton_dec_sset c) = A, from --c ∉ A
    begin 
      apply eq_of_homotopy, intro c', 
      change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _, hinduction A c' with p',
      all_goals { hinduction singleton_dec_sset c c' with q }, all_goals { try { refl } }, 
      hinduction HC c' c with eq r nr, 
      { exact p⁻¹ ⬝ (ap A r)⁻¹ ⬝ p' }, 
      { change @decidable.rec (c' = c) _ _ _ (HC c' c) = _ at q, rwr eq at q, exact q } 
    end, 
    rwr <- q, assumption },
  { have q : dec_setminus A (singleton_dec_sset c) ∪ (singleton_dec_sset c) = A, from 
    begin 
      apply eq_of_homotopy, intro c', 
      change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _, hinduction A c' with p',
      all_goals { hinduction singleton_dec_sset c c' with q },
      all_goals { hinduction dec_setminus A (singleton_dec_sset c) c' with q' },
      all_goals { try { refl } }, all_goals { hsimp },
      exact (dec_setminus_inc _ _ c' q')⁻¹ ⬝ p',
      all_goals { try { rwr singleton_dec_sset_eq c c' q at p, exact p⁻¹ ⬝ p' } },
      change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at q', rwr p' at q', 
      rwr q at q', exact q'⁻¹
    end,
    have disj : dec_setminus A (singleton_dec_sset c) ∩ (singleton_dec_sset c) = 
                empty_dec_Subset C, 
      by rwr dec_inter_comm; exact dec_setminus_disjoint _ _, 
    rwr <- q, 
    exact @fin_disj_union_fin _ HC _ _ fin_dec_sm (singleton_dec_sset_fin c) disj } 
end 
   
@[hott]
def dec_sset_of_fin_sset_is_fin' {C : Set} [HC : decidable_eq C] {n : ℕ} : 
  Π {A B : dec_Subset C} [H : is_finite_dec_sset B] (p : H.fin.fin_bij.1 = n), 
    A ⊆ B -> is_finite_dec_sset A :=
begin
  hinduction n,
  { intros A B H p inc, 
    hinduction H with fin_B, hinduction fin_B with nbB, 
    hinduction nbB with nB ex_bij_B, change nB = 0 at p, 
    hinduction ex_bij_B with bij_B,
    apply is_finite_dec_sset.mk, apply is_finite.mk, fapply sigma.mk, 
    exact 0, apply tr, fapply has_inverse_to_bijection, 
    { intro a, hinduction a with a el_a,  
      have p' : ↥(fin_Set nB) = ↥(fin_Set 0), by rwr p,
      rwr <- p', apply bij_B.map, exact ⟨a, inc a el_a⟩ }, 
    { intro m, hinduction nat.not_lt_zero m.1 m.2 }, 
    { fapply is_set_inverse_of.mk, 
        intro m, hinduction nat.not_lt_zero m.1 m.2,
        intro a, hinduction a with a el_a,
        have m : ↥(fin_Set nB), from bij_B ⟨a, inc a el_a⟩,
        rwr p at m, hinduction nat.not_lt_zero m.1 m.2 } },
  { intros A B H p inc, 
    hinduction H with fin_B, hinduction fin_B with nbB, 
    hinduction nbB with nB ex_bij_B, change nB = n+1 at p, 
    hinduction ex_bij_B with bij_B,
    let f := (inv_bijection_of bij_B),
    have p' : (fin_Set nB) = (fin_Set (n+1)), by rwr p,
    rwr p' at f,
    let fn_sset := singleton_dec_sset (f ⟨n, nat.le_refl (n+1)⟩).1, 
    let smB := dec_setminus B fn_sset,
    have smB_bij : bijection (dec_pred_Set smB) (fin_Set n), from 
      inv_bijection_of (dec_sset_minus_el_bij f),
    apply fin_setminus_fin (f ⟨n, nat.le_refl (n+1)⟩).1,
    let H' : is_finite_dec_sset (smB) := 
                                      is_finite_dec_sset.mk (is_finite.mk ⟨n, tr smB_bij⟩), 
    have q : @card_fin_dec_sset _ smB H' = n, from rfl,
    exact @ih _ _ H' q (inc_dec_setminus_inc _ _ _ inc) }
end

@[hott]
def dec_sset_of_fin_sset_is_fin {C : Set} [HC : decidable_eq C] : 
  Π {A B : dec_Subset C} [H : is_finite_dec_sset B], A ⊆ B -> is_finite_dec_sset A :=
assume A B H inc, 
@dec_sset_of_fin_sset_is_fin' _ _ (@card_fin_dec_sset _ B H) A B H idp inc

/- The intersection of two decidable subsets is finite if one of the intersection sets is
   finite. -/
@[hott]
def fin_inter_fin_l {C : Set} [HC : decidable_eq C] {A B : dec_Subset C} :
  is_finite_dec_sset A -> is_finite_dec_sset (A ∩ B) := 
assume fin_A, @dec_sset_of_fin_sset_is_fin _ _ _ _ fin_A (inter_dec_sset_l A B)

@[hott]
def fin_inter_fin_r {C : Set} [HC : decidable_eq C] {A B : dec_Subset C} :
  is_finite_dec_sset B -> is_finite_dec_sset (A ∩ B) := 
assume fin_B, @dec_sset_of_fin_sset_is_fin _ _ _ _ fin_B (inter_dec_sset_r A B)

/- The union of two finite decidable subsets is finite. -/
@[hott]
def fin_union_fin {C : Set.{u}} [HC : decidable_eq C] {A B : dec_Subset C} :
  is_finite_dec_sset A -> is_finite_dec_sset B -> is_finite_dec_sset (A ∪ B) :=
begin 
  intros fin_A fin_B, rwr dec_union_setminus_union, fapply fin_disj_union_fin.{u u},
  { exact fin_A }, 
  { fapply @dec_sset_of_fin_sset_is_fin.{u u} _ _ _ _ fin_B, exact dec_setminus_inc _ _ }, 
  { exact dec_setminus_disjoint _ _ },
  { exact HC }
end

/- The union of finitely many finite decidable subsets is finite. -/
@[hott]
def dec_fin_union_fin {A : Set.{u}} [HC : decidable_eq A] {n : ℕ} 
  (f : fin_Set n -> dec_Subset A) :
  (Π (m : fin_Set n), is_finite_dec_sset (f m)) -> is_finite_dec_sset (dec_fin_iUnion f) := 
begin
  hinduction n, 
  { intro fin_comp, change is_finite_dec_sset (⋃ᵢ f), rwr empty_dec_iUnion_empty, 
    exact empty_dec_sset_fin.{u u} },
  { intro fin_comp, change is_finite_dec_sset (⋃ᵢ f), rwr dec_fin_iUnion_union, 
    fapply fin_union_fin.{u}, 
    { apply ih (λ (m : fin_Set n), f (fin_Set_lift (nat.le_succ n) m)), 
      intro m, exact fin_comp (fin_Set_lift (nat.le_succ n) m) },
    { exact fin_comp _ },
    { exact HC } }
end

/- Some algebra rules for finite decidable subsets constructed from lists. -/
@[hott]
def union_dec_sset_of_list {A : Set.{u}} [HC : decidable_eq A] {l₁ l₂: list A} :
  dec_sset_of_list l₁ ∪ dec_sset_of_list l₂ = dec_sset_of_list (l₁ ++ l₂) :=
begin
  have p : list.length l₁ ≤ list.length (l₁ ++ l₂), from 
    begin rwr list_length_append l₁ l₂, exact nat.le_add_right _ _ end,
  have p' : list.length l₂ ≤ list.length (l₁ ++ l₂), from 
    begin rwr list_length_append l₁ l₂, exact nat.le_add_left _ _ end,
  apply dec_sset_eq_of_sset_eq, rwr dec_union_is_union,
  rwr dec_sset_of_list_to_sset, rwr dec_sset_of_list_to_sset, rwr dec_sset_of_list_to_sset,
  apply (sset_eq_iff_inclusion _ _).2, fapply pair,
  { intros a a_el, hinduction a_el, hinduction a_1, 
    { hinduction val with af, apply tr, fapply fiber.mk,  
      { exact fin_Set_lift p af.1 }, 
      { change fin_map_of_list _ ⟨af.1.1, _⟩ = a, rwr <- fin_map_of_list_el,
        apply λ p, p ⬝ af.2, hinduction af.1, rwr <- fin_map_of_list_el l₁, hsimp,
        rwr <- list_append_el₁ l₁ l₂ fst snd, exact list_nth_le_eq _ _ } },
    { hinduction val with af, apply tr, fapply fiber.mk,
      { fapply dpair, exact list.length l₁ + af.1.1, 
        rwr list_length_append l₁ l₂, exact nat.add_lt_add_left af.1.2 _ },
      { change fin_map_of_list _ ⟨list.length l₁ + af.1.1, _⟩ = a, 
        rwr <- fin_map_of_list_el, apply λ p, p ⬝ af.2, hinduction af.1,
        rwr <- fin_map_of_list_el l₂, rwr <- list_append_el₂ l₁ l₂ fst snd,
        exact list_nth_le_eq _ _ } } },
  { intros a a_el, hinduction a_el, hinduction a_1, apply tr,
    hinduction nat.lt_sum_ge point.1 (list.length l₁), 
    { apply sum.inl, apply tr, fapply fiber.mk, 
      { exact ⟨point.1, val⟩ },
      { rwr <- fin_map_of_list_el, hinduction point, 
        rwr <- fin_map_of_list_el at point_eq, rwr <- point_eq, 
        rwr <- list_append_el₁ l₁ l₂ fst val, exact list_nth_le_eq _ _ } },
    { apply sum.inr, apply tr, fapply fiber.mk, 
      { fapply dpair, exact point.1 - (list.length l₁), 
        fapply nat.sub_lt_of_lt_add, rwr <- list_length_append, exact point.2, exact val },
      { rwr <- point_eq, hinduction point, rwr <- fin_map_of_list_el l₂, 
        rwr <- fin_map_of_list_el, rwr <- list_append_el₂ l₁ l₂, 
        apply list_nth_le_eq', exact nat.add_sub_cancel_left'' _ _ val } } }
end

end subset

end hott