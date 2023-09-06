import sets.algebra

--subset sets.finite sets.axioms hott.types.prod hott.types.nat.sub

universes u v w
hott_theory

namespace hott
open hott.set subset prod trunc is_trunc sum

namespace subset

/- When dealing with variables of a first-order language we need inclusion of decidable 
   subsets and their properties, and that intersections, unions and complements of 
   decidable subsets are again decidable. -/
@[hott]
def dec_inc_to_inc {S : Set} {A B : dec_Subset S} : 
  A ⊆ B -> dec_sset_to_sset A ⊆ dec_sset_to_sset B :=
begin 
  intros dec_inc x el_A, hinduction A x, 
  { change ↥(@Two.rec (λ t, Prop) _ _ _) at el_A, rwr _h at el_A, hinduction el_A },
  { change ↥(@Two.rec (λ t, Prop) _ _ _),
    have p : B x = Two.one, from dec_inc x _h, rwr p, exact true.intro } 
end

@[hott]
def inc_to_dec_inc {S : Set} {A B : dec_Subset S} : 
  dec_sset_to_sset A ⊆ dec_sset_to_sset B -> A ⊆ B :=
begin 
  intros inc x el_A, 
  have p : A x = Two.one, from el_A,
  have P : ↥(dec_sset_to_sset B x), from 
    begin apply inc x, change ↥(@Two.rec (λ t, Prop) _ _ _), rwr p, exact true.intro end, 
  change ↥(@Two.rec (λ t, Prop) _ _ _) at P, hinduction B x, rwr _h at P, hinduction P,
  exact _h 
end 

@[hott]
def dec_subset_refl {A : Set.{u}} (B : dec_Subset A) : B ⊆ B :=
  inc_to_dec_inc (subset_refl (dec_sset_to_sset B))

@[hott, hsimp]
def dec_subset_trans {A : Set.{u}} (B C D : dec_Subset A) : 
  B ⊆ C -> C ⊆ D -> B ⊆ D :=
begin 
  intros BC_ss CD_ss, apply inc_to_dec_inc, 
  exact subset_trans _ _ _ (dec_inc_to_inc BC_ss) (dec_inc_to_inc CD_ss) 
end

@[hott, reducible]
protected def dec_inter {A : Set.{u}} (S₁ S₂ : dec_Subset A) : dec_Subset A :=
λ a : A, @Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) 
                                 (λ t, Two.rec Two.zero Two.zero t) 
                                 (λ t, Two.rec Two.zero Two.one t) (S₁ a) (S₂ a)

@[hott, instance]
def dec_subsets_have_dec_inter {A : Set.{u}} : has_inter (dec_Subset A) :=
  has_inter.mk (λ B C, hott.subset.dec_inter B C)

@[hott]
def dec_inter_is_inter {A : Set.{u}} (S₁ S₂ : dec_Subset A) : 
  dec_sset_to_sset (S₁ ∩ S₂) = dec_sset_to_sset S₁ ∩ dec_sset_to_sset S₂ :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } },
    apply pair, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro, 
                change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₂, exact true.intro },
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    change ↥((@Two.rec (λ t : Two, Prop) _ _ _) and (@Two.rec (λ t : Two, Prop) _ _ _)) 
           at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { rwr t₁ at inc, rwr t₂ at inc, hinduction inc },
    all_goals { try {hinduction fst } }, all_goals { try {hinduction snd } },
    exact true.intro }
end 

@[hott]
def dec_inter_comm {A : Set.{u}} (S₁ S₂ : dec_Subset A) : S₁ ∩ S₂ = S₂ ∩ S₁ :=
begin
  apply dec_sset_eq_of_sset_eq, rwr dec_inter_is_inter, rwr dec_inter_is_inter, 
  rwr inter.symm
end

@[hott]
def inter_dec_sset_l {A : Set.{u}} (S₁ S₂ : dec_Subset A) : (S₁ ∩ S₂) ⊆ S₁ := 
  begin apply inc_to_dec_inc, rwr dec_inter_is_inter, exact inter_sset_l _ _ end

@[hott]
def inter_dec_sset_r {A : Set.{u}} (S₁ S₂ : dec_Subset A) : (S₁ ∩ S₂) ⊆ S₂ := 
  begin apply inc_to_dec_inc, rwr dec_inter_is_inter, exact inter_sset_r _ _ end


@[hott, reducible]
protected def dec_union {A : Set.{u}} (S₁ S₂ : dec_Subset A) : dec_Subset A :=
λ a : A, @Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) 
                                 (λ t, Two.rec Two.zero Two.one t) 
                                 (λ t, Two.rec Two.one Two.one t) (S₁ a) (S₂ a)

@[hott, instance]
def dec_subsets_have_dec_union {A : Set.{u}} : has_union (dec_Subset A) :=
  has_union.mk (λ B C, hott.subset.dec_union B C)

@[hott]
def dec_union_is_union {A : Set.{u}} (S₁ S₂ : dec_Subset A) : 
  dec_sset_to_sset (S₁ ∪ S₂) = dec_sset_to_sset S₁ ∪ dec_sset_to_sset S₂ :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } },
    all_goals { change ↥(∥ _ ∥), apply tr },  
    apply sum.inr, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₂, exact true.intro, 
    apply sum.inl, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro,
    apply sum.inl, change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro },
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    change ↥((@Two.rec (λ t : Two, Prop) _ _ _) or (@Two.rec (λ t : Two, Prop) _ _ _)) 
           at inc,
    hinduction S₁ a with t₁, all_goals { hinduction S₂ a with t₂ }, 
    all_goals { rwr t₁ at inc, rwr t₂ at inc, hinduction inc with sum, hinduction sum },
    all_goals { try {hinduction val } }, 
    all_goals { try { exact true.intro } } }
end

@[hott]
def union_dec_sset_l {A : Set.{u}} (S₁ S₂ : dec_Subset A) : S₁ ⊆ (S₁ ∪ S₂) := 
  begin apply inc_to_dec_inc, rwr dec_union_is_union, exact union_sset_l _ _ end

@[hott]
def union_dec_sset_r {A : Set.{u}} (S₁ S₂ : dec_Subset A) : S₂ ⊆ (S₁ ∪ S₂) := 
  begin apply inc_to_dec_inc, rwr dec_union_is_union, exact union_sset_r _ _ end

/- Without further assumptions we can only show that finite intersections and unions of 
   decidable subsets are decidable subsets. -/
@[hott, reducible]
def dec_fin_iInter {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  dec_Subset A :=
begin 
  hinduction n, exact λ a : A, Two.one, 
  exact subset.dec_inter (ih (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) 
                         (f ⟨n, nat.le_refl (n+1)⟩)
end

@[hott, instance]
def dec_ssets_have_ind_inter (A : Set.{u}) {n : ℕ} : 
  @has_ind_inter (dec_Subset A) (fin_Set n) :=
has_ind_inter.mk (λ f, @dec_fin_iInter A n f)  

@[hott]
def dec_fin_iInter_is_iInter {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  dec_sset_to_sset (⋂ᵢ f) = ⋂ᵢ (λ m : fin_Set n, dec_sset_to_sset (f m)) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, apply prop_to_prop_resize, hinduction n, 
      intro m, hinduction nat.not_lt_zero m.1 m.2,
      have p : (⋂ᵢ f) = (⋂ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∩ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
      rwr p at inc, rwr dec_inter_is_inter at inc, 
      intro m, hinduction m with m q, change ↥(dec_sset_to_sset (f ⟨m, q⟩) a),
      hinduction nat.eq_sum_lt_of_le q, 
        have q : sigma.mk m q = ⟨n, nat.le_refl (n + 1)⟩, from
        begin 
          fapply sigma.sigma_eq, exact (nat.succ.inj val), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end, 
        rwr q, exact inc.2, 
        have q' : m < n, from nat.lt_of_succ_lt_succ val,
        let f' := λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩,
        have r : f ⟨m, q⟩ = f' ⟨m, q'⟩, from 
        begin 
          change _ = f ⟨m, nat.le.step q'⟩, apply ap f, fapply sigma.sigma_eq,
          refl, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end,
        rwr r, exact ih f' inc.1 ⟨m, q'⟩ },
  { intros a inc, hinduction n,
    exact true.intro,
    have p : (⋂ᵢ f) = (⋂ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∩ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
    rwr p, rwr dec_inter_is_inter, apply pair,
    apply ih (λ (m : ↥(fin_Set n)), f ⟨m.fst, nat.le.step m.snd⟩), 
    apply prop_to_prop_resize, intro m,  
    exact prop_resize_to_prop inc ⟨m.fst, nat.le.step m.snd⟩,
    exact prop_resize_to_prop inc ⟨n, nat.le_refl (n+1)⟩ }
end

@[hott]
def dec_fin_iInter_inc {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  Π (m : fin_Set n), ⋂ᵢ f ⊆ f m :=
begin 
  intro m, apply inc_to_dec_inc, rwr dec_fin_iInter_is_iInter, exact sset_iInter _ m
end 

@[hott, reducible]
def dec_fin_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  dec_Subset A :=
begin 
  hinduction n, exact λ a : A, Two.zero, 
  exact subset.dec_union (ih (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) 
                         (f ⟨n, nat.le_refl (n+1)⟩)
end                                                      

@[hott, instance]
def dec_ssets_have_fin_ind_union (A : Set.{u}) {n : ℕ} (f : fin_Set n -> dec_Subset A) : 
  @has_ind_union (dec_Subset A) (fin_Set n) f :=
has_ind_union.mk f (@dec_fin_iUnion A n f)

@[hott]
def dec_fin_iUnion_is_iUnion {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  dec_sset_to_sset (⋃ᵢ f) = ⋃ᵢ (λ m : fin_Set n, dec_sset_to_sset (f m)) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, apply prop_to_prop_resize, hinduction n, 
    hinduction inc,
    have p : (⋃ᵢ f) = (⋃ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∪ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
    rwr p at inc, rwr dec_union_is_union at inc,
    hinduction inc with inc, hinduction inc with inc₁ inc₂,
      hinduction ih _ inc₁ with eq₁ i_inc₁, apply tr, fapply sigma.mk, 
        exact ⟨i_inc₁.1.1, nat.le.step i_inc₁.1.2⟩, exact i_inc₁.2,
      apply tr, exact ⟨⟨n, nat.le_refl (n + 1)⟩, inc₂⟩ },
  { intros a inc, hinduction n,
      hinduction prop_resize_to_prop inc with eq i_inc, -- n=0
      hinduction nat.not_lt_zero i_inc.1.1 i_inc.1.2,      
      hinduction prop_resize_to_prop inc with eq i_inc, clear eq, -- n -> n+1
      have p : (⋃ᵢ f) = (⋃ᵢ (λ m : fin_Set n, f ⟨m.1, nat.le.step m.2⟩)) ∪ 
                        (f ⟨n, nat.le_refl (n+1)⟩), from rfl,
      rwr p, rwr dec_union_is_union, apply tr, 
      hinduction nat.eq_sum_lt_of_le i_inc.1.2,
        apply sum.inr,                                        -- m = n
        have q : i_inc.1 = ⟨n, nat.le_refl (n + 1)⟩, from
        begin 
          fapply sigma.sigma_eq, exact (nat.succ.inj val), 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end, 
        rwr <- q, exact i_inc.2,
        apply sum.inl, apply ih (λ m, f ⟨m.fst, nat.le.step m.snd⟩),    -- m < n 
        apply prop_to_prop_resize, apply tr, fapply sigma.mk,
        have r : i_inc.1.1 < n, from nat.lt_of_succ_lt_succ val, 
        exact ⟨i_inc.1.1, r⟩, 
        change ↥(a∈dec_sset_to_sset (f _)), hsimp,
        have r' : i_inc.1 = ⟨i_inc.fst.fst, nat.le.step (nat.lt_of_succ_lt_succ val)⟩, from
        begin 
          hinduction i_inc.1, fapply sigma.sigma_eq, refl, 
          apply pathover_of_tr_eq, exact is_prop.elim _ _ 
        end,
        rwr <- r', exact i_inc.2 }
end

@[hott]
def dec_fin_iUnion_union {A : Set.{u}} {n : ℕ} (f : fin_Set (n+1) -> dec_Subset A) :
  ⋃ᵢ f = ⋃ᵢ (λ m : fin_Set n, f (fin_Set_lift (nat.le_succ n) m)) ∪ 
                                                         (f ⟨n, nat.le_refl (n+1)⟩) :=
begin
  let f' : fin_Set (n+1) -> Powerset A := (λ m, @dec_sset_to_sset A (f m)),
  apply dec_sset_eq_of_sset_eq, rwr dec_fin_iUnion_is_iUnion, rwr dec_union_is_union,  
  rwr dec_fin_iUnion_is_iUnion, apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { apply @iUnion_sset.{u 0} A (fin_Set (n+1)) f', intro m, 
    hinduction nat.eq_sum_lt_of_le m.2, 
    { have q : m = ⟨n, nat.le_refl (n + 1)⟩, from fin_Set_eq (nat.succ.inj val),
      have p : f' m = dec_sset_to_sset (f ⟨n, nat.le_refl (n + 1)⟩), by rwr q,
      rwr p, exact union_sset_r _ _ },
    { have p : f' m = (λ (m' : fin_Set n), dec_sset_to_sset (f (fin_Set_lift 
                (nat.le_succ n) m'))) (fin_Set_desc m (nat.le_of_succ_le_succ val)), from 
        begin hsimp, apply ap dec_sset_to_sset, apply ap f, apply fin_Set_eq, refl end,
      rwr p, apply subset_trans _ _ _ _ (union_sset_l _ _), 
      exact sset_iUnion _ (fin_Set_desc m (nat.le_of_succ_le_succ val)) } },
  { apply inc_inc_union_inc, 
    { apply @iUnion_sset.{u 0} A (fin_Set n), intro m, 
      change ↥((λ (m : fin_Set (n + 1)), dec_sset_to_sset (f m)) 
                                (fin_Set_lift (nat.le_succ n) m) ⊆ ⋃ᵢ _), 
      exact sset_iUnion _ (fin_Set_lift (nat.le_succ n) m) },
    { change ↥((λ (m : fin_Set (n + 1)), dec_sset_to_sset (f m)) 
                                         ⟨n, nat.le_refl (n + 1)⟩ ⊆ ⋃ᵢ _), 
      apply sset_iUnion (λ (m : fin_Set (n + 1)), dec_sset_to_sset (f m)) } }
end   

@[hott]
def empty_dec_iUnion_empty {A : Set.{u}} (f : fin_Set 0 -> dec_Subset A) :
  ⋃ᵢ f = empty_dec_Subset A :=
begin
  apply dec_sset_eq_of_sset_eq, rwr dec_fin_iUnion_is_iUnion,
  rwr empty_dec_sset_empty_sset, 
  have p : (⋃ᵢλ (m : ↥(fin_Set 0)), dec_sset_to_sset (f m)) = 
      ⋃ᵢ((λ (m : ↥(fin_Set 0)), dec_sset_to_sset (f m)) ∘ bij_empty_fin), from
    iUnion_index_bij (λ m, dec_sset_to_sset (f m)) bij_empty_fin,
  rwr p, exact empty_iUnion_empty _
end

@[hott]
def dec_fin_iUnion_inc {A : Set.{u}} {n : ℕ} (f : fin_Set n -> dec_Subset A) :
  Π (m : fin_Set n), f m ⊆ ⋃ᵢ f :=
begin
  intro m, apply inc_to_dec_inc, rwr dec_fin_iUnion_is_iUnion, exact sset_iUnion _ m 
end  

/- If `A` has decidable equality and the underlying sets of intersection 
   and union are finite then intersection and union are decidable, since all finite 
   subsets of `A` are decidable, see [sets.finite].-/
@[hott]
def fin_iUnion_dec_sset {A : Set.{u}} [decidable_eq A] {I : Set} 
  (f : I -> dec_Subset A) [is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] : 
  dec_Subset A :=
finite_sset_to_dec_sset.{u u u} (⋃ᵢ (λ i, dec_sset_to_sset (f i))) 

@[hott, instance]
def fin_iUnion_dec_sset_have_ind_union {A : Set.{u}} [H : decidable_eq A] {I : Set}
  (f : I -> dec_Subset A) [Hf : is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] : 
  @has_ind_union (dec_Subset A) I f :=
has_ind_union.mk f (fin_iUnion_dec_sset f)

@[hott]
def fin_iUnion_dec_sset_is_iUnion {A : Set.{u}} [decidable_eq A] {I : Set.{v}}
  (f : I -> dec_Subset A) [Hf : is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] :
  dec_sset_to_sset (⋃ᵢ f) = ⋃ᵢ (λ i : I, dec_sset_to_sset (f i)) :=
begin
  change dec_sset_to_sset (finite_sset_to_dec_sset _) = _, rwr finite_dec_sset_is_sset
end

@[hott]
def fin_iUnion_dec_sset_inc {A : Set.{u}} [decidable_eq A] {I : Set} 
  (f : I -> dec_Subset A) [is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (f i))))] :
  Π i : I, f i ⊆ (⋃ᵢ f) :=
begin
  intro i, apply inc_to_dec_inc, rwr fin_iUnion_dec_sset_is_iUnion, 
  exact sset_iUnion (λ (i : ↥I), dec_sset_to_sset (f i)) i 
end 

@[hott]
def fin_iInter_dec_sset {A : Set.{u}} [decidable_eq A] {I : Set} 
  (f : I -> dec_Subset A) [is_finite (pred_Set (⋂ᵢ (λ i, dec_sset_to_sset (f i))))] : 
  dec_Subset A :=
finite_sset_to_dec_sset (⋂ᵢ (λ i, dec_sset_to_sset (f i)))

/- The complement of a decidable subset is decidable. -/
@[hott]
protected def dec_complement {A : Set.{u}} (U : dec_Subset A) : dec_Subset A :=
  λ x : A, @Two.rec (λ t : Two, Two) Two.one Two.zero (U x) 

@[hott, instance]
def dec_sets_have_compl (A : Set) : @has_complement (dec_Subset A) :=
  has_complement.mk (λ U, subset.dec_complement U)

@[hott]
def dec_compl_is_compl {A : Set} (U : dec_Subset A) : 
  dec_sset_to_sset (𝒞 U) = 𝒞 (dec_sset_to_sset U) :=
begin 
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, hinduction U a with t,
    intro inc', change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc', -- U a = zero
    rwr t at inc', hinduction inc',
    have p : (𝒞 U) a = Two.zero, from           -- U a = one
        begin change (@Two.rec (λ t : Two, Two) _ _ _) = _, rwr t end,  
    change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc, rwr p at inc, hinduction inc },
  { intros a inc, hinduction U a with t, 
      have p : (𝒞 U) a = Two.one, from           -- U a = zero
        begin change (@Two.rec (λ t : Two, Two) _ _ _) = _, rwr t end, 
      change ↥(@Two.rec (λ t : Two, Prop) _ _ ((𝒞 U) a)), rwr p, exact true.intro, 
      have inc' : ↥(a ∈ dec_sset_to_sset U), from -- U a = one
        begin change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t, exact true.intro end,  
      hinduction inc inc' } 
end

/- The set-minus of two decidable subsets is decidable. -/
@[hott]
def dec_setminus {A : Set.{u}} (U V : dec_Subset A) : dec_Subset A :=
  λ a : A, @Two.rec (λ t : Two, Two -> Two) 
                       (λ t', @Two.rec (λ t', Two) Two.zero Two.zero (V a))
                       (λ t', @Two.rec (λ t', Two) Two.one Two.zero (V a)) (U a) (V a)

@[hott]
def dec_setminus_is_setminus {A : Set.{u}} (U V : dec_Subset A) :
  dec_sset_to_sset (dec_setminus U V) = 
                                 setminus (dec_sset_to_sset U) (dec_sset_to_sset V) :=
begin
  apply (sset_eq_iff_inclusion _ _).2, apply pair,
  { intros a inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)) at inc,
    hinduction U a with t₁, all_goals { hinduction V a with t₂ }, 
    all_goals { try { rwr t₁ at inc, rwr t₂ at inc, hinduction inc } }, apply pair, 
    change ↥(@Two.rec (λ t : Two, Prop) _ _ _), rwr t₁, exact true.intro, 
    intro inc, change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc, rwr t₂ at inc, 
    hinduction inc },
  { intros a inc, 
    change ↥(@Two.rec (λ t : Two, Prop) _ _ 
                       (@Two.rec (λ t : Two.{u}, (Two.{u} -> Two.{u})) _ _ _ _)),
    hinduction inc with inc₁ inc₂,
    hinduction U a with t₁, all_goals { hinduction V a with t₂ }, 
    all_goals { try { change ↥(@Two.rec (λ t : Two, Prop) _ _ _) at inc₁, 
                      rwr t₁ at inc₁, hinduction inc₁ } },
    all_goals { hsimp }, exact true.intro, 
    change ↥(Not (@Two.rec (λ t : Two, Prop) _ _ _)) at inc₂, rwr t₂ at inc₂, 
    hinduction inc₂ true.intro }
end

@[hott]
def dec_setminus_disjoint  {A : Set.{u}} (U V : dec_Subset A) : 
  V ∩ (dec_setminus U V) = empty_dec_Subset A :=
begin 
  apply dec_sset_eq_of_sset_eq, rwr dec_inter_is_inter, rwr dec_setminus_is_setminus,
  rwr empty_dec_sset_empty_sset, rwr setminus_disjoint
end

@[hott]
def dec_setminus_inc {A : Set.{u}} (U V : dec_Subset A) : dec_setminus U V ⊆ U :=
begin apply inc_to_dec_inc, rwr dec_setminus_is_setminus, exact set_minus_inc _ _ end

@[hott]
def inc_dec_setminus_inc {A : Set.{u}} (U V W : dec_Subset A) : 
  U ⊆ V -> dec_setminus U W ⊆ dec_setminus V W :=
begin 
  intros dec_ss, apply inc_to_dec_inc, rwr dec_setminus_is_setminus,
  rwr dec_setminus_is_setminus, exact inc_setminus_inc _ _ _ (dec_inc_to_inc dec_ss) 
end

@[hott]
def dec_set_minus_inc_impl {A : Set.{u}} [H : has_dec_elem A] (U V W : dec_Subset A) : 
  dec_setminus U V ⊆ W -> U ⊆ (W ∪ V) := 
begin 
  intro dec_sm_ss, apply inc_to_dec_inc, rwr dec_union_is_union,
  apply @set_minus_inc_impl _ _ _ _ H, rwr <- dec_setminus_is_setminus,
  apply dec_inc_to_inc, exact dec_sm_ss 
end

@[hott]
def dec_setminus_single_neq {A : Set.{u}} [H : decidable_eq A] {U : dec_Subset A} {a : A} 
  (el : a ∈ U) : Π (a' : A), a' ∈ dec_setminus U (singleton_dec_sset a) -> a' ≠ a :=
begin
  intros a' el' p, rwr p at el', change U a = Two.one at el, 
  change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = _ at el', rwr el at el', 
  have p : singleton_dec_sset a a = Two.one, from singleton_dec_sset_el a,
  rwr p at el', hsimp at el', hinduction encode_Two _ _ el'
end

@[hott]
def dec_union_setminus_union {A : Set.{u}} (U V : dec_Subset A) : 
  U ∪ V = U ∪ (dec_setminus V U) :=
begin 
  apply eq_of_homotopy, intro a, 
  hinduction U a with p, all_goals { hinduction V a with q }, 
  all_goals { change @Two.rec (λ t : Two, Two -> Two) _ _ _ _ = 
    @Two.rec (λ t : Two, Two -> Two) _ _ _ (@Two.rec (λ t : Two, Two -> Two) _ _ _ _),
    rwr p, rwr q }
end


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

set_option pp.universes true

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

end subset

end hott