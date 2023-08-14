import sets.algebra init2 sets.axioms sets.finite

universes v v' u u' w 
hott_theory

namespace hott
open hott.eq hott.set hott.subset hott.is_trunc hott.is_equiv hott.equiv 

/- Categories in the algebraic hierarchy are categories of structured sets. The structures can
   be constructed by an instance of a more general technique: as the model structure of an 
   (algebraic) first-order theory built on a first-order signature in a category with suitable 
   properties. The Ω-structures made up of functions and relations on sets in [HoTT-Book], 
   Sec.9.8) are another example of this technique, but the more general construction also 
   allows the construction of categories of topological groups or locally ringed sheaves. 
   
   We mainly follow the introduction to categorical model theory by [Caramello14]. 

   First-order signatures prescribe the types of arguments and the arity of functions and 
   relations in a first-order theory. 
   
   For infinitary conjunctions and disjunctions we need index sets, which we fix to universe 
   level 0 and only allow a choice from a set of universe level 0, to avoid universe problems.
   The idea of a Grothendieck universe or a von Neumann universe/cumulitative hierarchy does
   not help because we cannot quantify over a type of universe level 0 without raising the 
   universe level to 1.
   
   We also need a restriction on contexts because too large sets of variables may not 
   allowed to be index sets of products in interpreting categories. -/
namespace signature

/- Labels allow to distinguish variables of the same sort. 

   Usually, the labels will be countable, for example strings, and there will be only
   finitely many sorts, so decidable equality is automatic. -/
@[hott]
structure var (labels : dec_Set.{0}) (sorts : dec_Set.{0}) :=
  (label : labels)
  (sort : sorts) 

/- The following three lemmas should be produced automatically. -/
@[hott]
def var_eq {labels : dec_Set.{0}} {sorts : dec_Set.{0}} {x₁ x₂ : var labels sorts} : 
  (x₁.label = x₂.label) -> (x₁.sort = x₂.sort) -> (x₁ = x₂) :=
begin
  intros p_label p_sort, 
  hinduction x₁ with x₁ s₁, hinduction x₂ with x₂ s₂,
  apply ap011 var.mk p_label p_sort
end    

@[hott]
def var_eq_eta {labels : dec_Set.{0}} {sorts : dec_Set.{0}} {x₁ x₂ : var labels sorts} 
  (p : x₁ = x₂) : var_eq (ap var.label p) (ap var.sort p) = p := 
begin hinduction p, hinduction x₁, reflexivity end    
    
@[hott, instance]
def var_is_set {labels : dec_Set.{0}} {sorts : dec_Set.{0}} : is_set (var labels sorts) :=
begin
  fapply is_set.mk, intros x y p q, 
  rwr <- var_eq_eta p, rwr <- var_eq_eta q,
  apply ap011 var_eq, apply is_set.elim, apply is_set.elim
end   

@[hott, instance]
def var_is_dec {labels : dec_Set.{0}} {sorts : dec_Set.{0}} : 
  decidable_eq (var labels sorts) :=
begin 
  intros x y, hinduction x with xl xs, hinduction y with yl ys, 
  hinduction labels.dec xl yl with ihl pl, 
  all_goals { hinduction sorts.dec xs ys with ihs ps }, 
    exact decidable.inl (ap011 var.mk pl ps), 
    apply decidable.inr, intro p, hinduction val (ap var.sort p), 
    apply decidable.inr, intro p, hinduction val (ap var.label p), 
    apply decidable.inr, intro p, hinduction val (ap var.label p) 
end

/- In a first-order signature we want decidable sets of operations, relations and index 
   sets for infinite con- and disjunctions. But we only allow finite arities for 
   operations and relations. -/
@[hott]
structure fo_signature :=
  (labels : dec_Set.{0}) 
  (sorts : dec_Set.{0}) 
  (ops : dec_Set.{0}) 
  (ops_arity : Π (o : ops), ℕ)
  (ops_source : Π (o : ops), fin_Set (ops_arity o) -> sorts)
  (ops_target : Π (o : ops), sorts)
  (rels : dec_Set.{0})
  (rels_arity : Π (r : rels), ℕ)
  (rels_comp : Π {r : rels}, fin_Set (rels_arity r) -> sorts)
  (ind_Set : dec_Set.{0})  --set indexing all index sets
  (I : ind_Set -> dec_Set.{0}) 
/- If we don't restrict the possible index sets of infinte con- and disjunction to a set
   the type of formulas is not a set. -/


namespace term

@[hott] 
inductive term_of_sort {sign : fo_signature} : sign.sorts -> Type 
| var (s : sign.sorts) (x : var sign.labels sign.sorts) (pv : x.sort = s) : 
                                                                       term_of_sort s      
| op (s : sign.sorts) (o : sign.ops) (pot : sign.ops_target o = s)
     (args : Π (oa : fin_Set (sign.ops_arity o)), term_of_sort (sign.ops_source o oa)) : 
     term_of_sort s

@[hott, reducible]
protected def code {sign : fo_signature} : Π {s₁ s₂ : sign.sorts}, 
  term_of_sort s₁ -> term_of_sort s₂ -> Type :=
begin
  intros s₁ s₂ t₁, revert s₁ t₁ s₂, intros s₁ t₁,
  hinduction t₁ with s₁ x₁ px₁ s₁ o₁ pot₁ args₁ ih₁,
  all_goals { intros s₂ t₂, hinduction t₂ with s₂ x₂ px₂ s₂ o₂ pot₂ args₂ ih₂ },
  exact x₁ = x₂, exact Zero, exact Zero,
  exact Σ (q : o₁ = o₂), Π (oa₁ : fin_Set (sign.ops_arity o₁)), ih₁ oa₁ (args₂ (q ▸ oa₁))  
end  
/- The equation compiler produces a non-hott term when we use 
   pattern-matching to define `code`: 
| s₁ s₂ (term.var _ v₁ pv₁) (term.var _ v₂ pv₂) := v₁ = v₂
| s₁ s₂ (term.var _ v₁ pv₁) (term.op _ o₂ pot₂ args₂) := Zero
| s₁ s₂ (term.op _ o₁ pot₁ args₁) (term.var _ v₂ pv₂) := Zero
| s₁ s₂ (term.op _ o₁ pot₁ args₁) (term.op _ o₂ pot₂ args₂) :=  
    Σ (q : o₁ = o₂), Π (oa₁ : sign.ops_arity o₁), 
                       code (args₁ oa₁) (args₂ (q ▸ oa₁)) -/

@[hott, instance]
protected def code_is_prop  {sign : fo_signature} {s₁ s₂ : sign.sorts} : 
  Π (t₁ : term_of_sort s₁) (t₂ : term_of_sort s₂), 
    is_prop (term.code t₁ t₂) :=
begin
  intro t₁, revert s₁ t₁ s₂, intros s₁ t₁, 
  hinduction t₁ with s₁ x₁ px₁ s₁ o₁ pot₁ args₁ ih₁, 
  all_goals { intros s₂ t₂, hinduction t₂ with s₂ x₂ px₂ s₂ o₂ pot₂ args₂ ih₂, }, 
  { change is_prop (x₁ = x₂), apply is_prop.mk, intros q q', exact is_set.elim _ _ },
  { change is_prop Zero, apply_instance },
  { change is_prop Zero, apply_instance },
  { change is_prop (Σ (q : o₁ = o₂), Π (oa₁ : fin_Set (sign.ops_arity o₁)),
                        term.code (args₁ oa₁) (args₂ (q ▸ oa₁))),
    apply is_prop.mk, intros t₁_code t₂_code, fapply sigma.sigma_eq, 
    { exact is_set.elim _ _ },
    { apply pathover_of_tr_eq, apply eq_of_homotopy, intro oa₁, 
      exact @is_prop.elim _ (ih₁ oa₁ (args₂ (t₂_code.1 ▸ oa₁))) _ _ } }
end 

@[hott]
structure term (sign : fo_signature) :=
  (sort : sign.sorts)
  (expr : term_of_sort sort)

@[hott]
def term_eq_term {sign : fo_signature} (s : sign.sorts) :
  Π (t₁ t₂ : term_of_sort s), term.mk s t₁ = term.mk s t₂ -> t₁ = t₂ :=
begin
  intros t₁ t₂ q, let p := pathover_ap _ _ (apd term.expr q), 
  hsimp at p, have r : ap term.sort q = idp, from is_set.elim _ _, 
  rwr r at p, exact eq_of_pathover_idp p
end

@[hott]
protected def refl {sign : fo_signature} : 
  Π t : term sign, term.code t.expr t.expr :=
begin 
  intro term, hinduction term with s t, hinduction t,
  exact rfl , exact ⟨rfl, λ k, ih k⟩ 
end 

@[hott, reducible]
protected def ppred {sign : fo_signature} (t₀ : term sign) : ppred t₀ :=
  ppred.mk (λ t : term sign, term.code t₀.expr t.expr) (term.refl t₀)

@[hott, hsimp]
protected def decode {sign : fo_signature} : 
  Π {t₁ t₂ : term sign}, term.code t₁.expr t₂.expr -> t₁ = t₂ :=
begin
  intro t₁, hinduction t₁ with s₁ t₁, 
  hinduction t₁ with s₁ x₁ px₁ s₁ o₁ pot₁ args₁ ih₁,
  all_goals { intro t₂, hinduction t₂ with s₂ t₂, 
              hinduction t₂ with s₂ x₂ px₂ s₂ o₂ pot₂ args₂ ih₂ }, 
  { intro t_code, 
      have q : x₁ = x₂, from t_code, hinduction q, 
      have r : s₁ = s₂, from px₁⁻¹ ⬝ px₂, hinduction r,
      fapply apd011 term.mk, exact rfl, apply pathover_idp_of_eq, 
      exact ap (term_of_sort.var s₁ x₁) (is_set.elim _ _) },
  { intro t_code, hinduction t_code },
  { intro t_code, hinduction t_code },
  { intro t_code,       
    change Σ (q : o₁ = o₂), Π (oa₁ : fin_Set (sign.ops_arity o₁)),
                term.code (args₁ oa₁) (args₂ (q ▸ oa₁)) at t_code,
    hinduction t_code with q args_code, hinduction q,
    have ps : s₁ = s₂, from pot₁⁻¹ ⬝ pot₂, hinduction ps,
    have pot_eq : pot₁ = pot₂, from is_set.elim _ _, hinduction pot_eq,
    fapply apd011 term.mk, exact rfl, apply pathover_idp_of_eq,                 
    apply ap (term_of_sort.op s₁ o₁ pot₁), apply eq_of_homotopy, 
    intro oa₁,  
    have q : term.mk _ (args₁ oa₁) = term.mk _ (args₂ (idp ▸ oa₁)), from 
      begin exact @ih₁ oa₁ (term.mk _ (args₂ (idp ▸ oa₁))) (args_code oa₁) end, 
    rwr idp_tr oa₁ at q, exact term_eq_term _ _ _ q }
end  

@[hott]
def term_eq_equiv_code {sign : fo_signature} (t₀ : term sign) :
  Π (t : term sign), (t₀ = t) ≃ (term.code t₀.expr t.expr) :=
begin
  apply tot_space_contr_ppmap_id_eqv' _ (can_ppmap (term.ppred t₀)), 
  fapply is_contr.mk, exact ⟨t₀, term.refl t₀⟩, 
  intro t, hinduction t with t t_code, 
  change term.code t₀.expr t.expr at t_code,
  fapply sigma.sigma_eq,
  { exact term.decode t_code },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _}
end

@[hott, instance]
def term_is_set {sign : fo_signature} : is_set (term sign) :=
begin
  apply is_trunc_succ_intro, intros term₁ term₂, 
  exact is_trunc_equiv_closed_rev -1 (term_eq_equiv_code term₁ term₂) 
                                     (term.code_is_prop _ _)
end

end term

open term

/- Terms of a specific sort also form a set. -/
@[hott]
def term_eq {sign : fo_signature} {term₁ term₂ : term sign} : 
  Π (p : term₁.sort = term₂.sort), (term₁.expr =[p] term₂.expr) -> (term₁ = term₂) :=
begin
  intros p q, hinduction term₁ with s₁ t₁, hinduction term₂ with s₂ t₂, 
  exact apd011 term.mk p q
end 

@[hott]
def term_of_sort_of_term {sign : fo_signature} (s : sign.sorts) :
  (term_of_sort s) ≃ (Σ (t : term sign), t.sort = s) :=
begin 
  fapply equiv.mk, 
  { intro t, exact ⟨term.mk s t, rfl⟩ },
  { fapply adjointify, 
    { intro t, exact t.2 ▸ t.1.expr },
    { intro t, hsimp, fapply sigma.sigma_eq, 
      { fapply term_eq, 
        { hsimp, exact t.2⁻¹ },
        { hsimp, apply pathover_of_tr_eq, rwr idp_inv, hsimp } },
      { apply pathover_of_tr_eq, exact is_set.elim _ _ } },
    { intro t, hsimp } } 
end  

@[hott, instance]
def term_of_sort_is_set {sign : fo_signature} (s : sign.sorts) : 
  is_set (term_of_sort s) :=
begin apply is_trunc_equiv_closed_rev 0 (term_of_sort_of_term s), apply_instance end  


/- To define formulas we need the free variables of a term. -/
@[hott]
def free_vars_of_term {sign : fo_signature} : term sign -> 
  dec_Subset (to_Set (var sign.labels sign.sorts)) :=
begin 
  intro t, hinduction t, hinduction expr, 
  { exact singleton_dec_sset x }, 
  { exact dec_fin_iUnion ih }
end

@[hott, instance]
def free_vars_of_term_is_fin {sign : fo_signature} (t : term sign) : 
  is_finite_dec_sset (free_vars_of_term t) :=
begin
  apply is_finite_dec_sset.mk,
  hinduction t, hinduction expr,
  { change ↥(to_Set (var sign.labels sign.sorts)) at x,
    exact (singleton_dec_sset_fin.{0} x).fin },
  { change is_finite (pred_Set (dec_sset_to_sset (dec_fin_iUnion _))), 
    sorry }
end

/- Terms and later formulas and sequents should always only contain free variables from a 
   `context`, a decidable subset of the set of variables. -/
@[hott]
structure context (sign : fo_signature) := 
  (vars : dec_Subset (to_Set (var sign.labels sign.sorts)))

@[hott]
def context_eq {sign : fo_signature} {cont₁ cont₂ : context sign} : 
  (cont₁.vars = cont₂.vars) -> (cont₁ = cont₂) :=
begin
  intro p_vars, 
  hinduction cont₁ with vars₁ pred₁, hinduction cont₂ with vars₂ pred₂,
  apply ap context.mk p_vars
end    

@[hott]
def context_eq_refl {sign : fo_signature} (cont : context sign) : 
  context_eq (@idp _ (cont.vars)) = (@idp _ cont) :=
begin 
  hinduction cont, hsimp, change ap context.mk (@idp _ vars) = _, refl
end 

@[hott]
def context_eq_eta {sign : fo_signature} {cont₁ cont₂ : context sign} (p : cont₁ = cont₂) :
  context_eq (ap context.vars p) = p := 
begin hinduction p, hsimp, exact context_eq_refl cont₁ end 

@[hott, instance]
def cont_vars_is_set {sign : fo_signature} :
  is_set ((to_Set (var sign.labels sign.sorts)) -> Two.{0}) :=
begin 
  change is_set ((var sign.labels sign.sorts) -> Two_Set), 
  exact @is_set_map _ _ 
end

@[hott, instance]
def context_is_set {sign : fo_signature} : is_set (context sign) :=
begin 
  fapply is_set.mk, intros x y p q, 
  rwr <- context_eq_eta p, rwr <- context_eq_eta q,
  apply ap context_eq, apply is_set.elim _ _, exact cont_vars_is_set
end

@[hott]
structure term_in_context {sign : fo_signature} (cont : context sign) := 
  (t : term sign) 
  (in_cont : free_vars_of_term t ⊆ dec_sset_to_sset cont.vars)


/- Formulas in the first-order language built upon a first-order signature, together with 
   the free variables that they contain, are defined inductively.   -/
namespace formula

@[hott]
inductive formula (sign : fo_signature)
| eq_terms : Π (t₁ t₂ : term sign), (t₁.sort = t₂.sort) -> formula
| rel_terms : Π (r : sign.rels) (comp : Π (k : fin_Set (sign.rels_arity r)), 
                                           term_of_sort (sign.rels_comp k)), formula
| T : formula
| F : formula 
| conj : formula -> formula -> formula 
| disj : formula -> formula -> formula
| impl : formula -> formula -> formula 
| neg : formula -> formula
| ex : var sign.labels sign.sorts -> formula -> formula 
| univ : var sign.labels sign.sorts -> formula -> formula 
| inf_conj : Π {i : sign.ind_Set}, ((sign.I i) -> formula) -> formula 
| inf_disj : Π {i : sign.ind_Set}, ((sign.I i) -> formula) -> formula        

@[hott]
protected def code {sign : fo_signature} : formula sign -> formula sign -> Type :=
/- A match-expression does not work because we need proper induction. -/  
begin
  intro form₁, hinduction form₁ with t₁ t₂ p r comp f₁ f₂ ih₁ ih₂ f₁ f₂ ih₁ ih₂
                                     f₁ f₂ ih₁ ih₂ f ih x f ih x f ih i f ih i f ih,
  all_goals { intro form₂, 
              hinduction form₂ with t₁' t₂' p' r' comp' f₁' f₂' ih₁' ih₂' f₁' f₂' ih₁' ih₂'
                f₁' f₂' ih₁' ih₂' f' ih' x' f' ih' x' f' ih' i' f' ih' i' f' ih' },              
  exact (t₁ = t₁') × (t₂ = t₂'), --equality
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Σ (q : r = r'), comp =[q; λ s, Π (k : fin_Set (sign.rels_arity s)), --relations
                                         term_of_sort (sign.rels_comp k)] comp', 
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,                                       
  exact One, --T
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,                                       
  exact One, --F
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact prod (ih₁ f₁') (ih₂ f₂'), --conj
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact prod (ih₁ f₁') (ih₂ f₂'), --disj
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact prod (ih₁ f₁') (ih₂ f₂'), --impl
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact ih f',  --neg
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact prod (x = x') (ih f'),  --ex
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact prod (x = x') (ih f'),  --univ
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,  
  exact Σ (p : i = i'), Π j : sign.I i, ih j (f' (p ▸ j)), --inf_conj
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,  
  exact Σ (p : i = i'), Π j : sign.I i, ih j (f' (p ▸ j)) --inf_disj 
end  

@[hott]
def code_neg_form {sign : fo_signature} (f f' : formula sign) : 
  formula.code (formula.neg f) (formula.neg f') -> formula.code f f' :=
begin intro c, exact c end

@[hott, instance]
protected def code_is_prop  {sign : fo_signature} : 
  Π form₁ form₂ : formula sign, is_prop (formula.code form₁ form₂) :=
begin
  intro form₁, hinduction form₁ with t₁ t₂ p r comp f₁ f₂ ih₁ ih₂ f₁ f₂ ih₁ ih₂
                                     f₁ f₂ ih₁ ih₂ f ih x f ih x f ih i f ih i f ih,
  all_goals { intro form₂, 
              hinduction form₂ with t₁' t₂' p' r' comp' f₁' f₂' ih₁' ih₂' f₁' f₂' ih₁' ih₂'
                f₁' f₂' ih₁' ih₂' f' ih' x' f' ih' x' f' ih' i' f' ih' i' f' ih' }, 
  all_goals { try { exact Zero_is_prop } },
  all_goals { try { exact One_is_prop } }, 
  { apply is_prop.mk, intros q q', apply pair_eq, 
      exact is_prop.elim _ _, exact is_prop.elim _ _ }, 
  { apply is_prop.mk, intros code₁ code₂, 
    apply @sigma_Prop_eq (r = r') 
             (λ q, to_Prop (comp =[q; λ s, Π (k : sign.rels_arity s), 
                                              term_of_sort (sign.rels_comp k)] comp')),
    exact is_set.elim _ _ },  
  all_goals { try { apply is_prop.mk, intros code₁ code₂, apply pair_eq, 
    exact @is_prop.elim _ (ih₁ f₁') _ _, exact @is_prop.elim _ (ih₂ f₂') _ _ } },
  { apply is_prop.mk, intros code₁ code₂, exact @is_prop.elim _ (ih f') _ _ },
  all_goals { try { apply is_prop.mk, intros code₁ code₂, apply pair_eq, 
              exact is_prop.elim _ _, exact @is_prop.elim _ (ih f') _ _ } },
  
  all_goals { apply is_prop.mk, intros code₁ code₂, fapply sigma.sigma_eq, 
    exact is_prop.elim _ _ , apply pathover_of_tr_eq, apply eq_of_homotopy, intro x, 
    exact @is_prop.elim _ (ih x (f' (code₂.fst ▸[λ i, sign.I i] x))) _ (code₂.2 x) }
end  

@[hott]
protected def refl {sign : fo_signature} : Π t : formula sign, formula.code t t :=
begin 
  intro t, hinduction t, exact ⟨idp, idp⟩, exact ⟨idp, idpo⟩, 
  exact One.star, exact One.star,
  exact ⟨ih_a, ih_a_1⟩, exact ⟨ih_a, ih_a_1⟩, exact ⟨ih_a, ih_a_1⟩,
  exact ih, exact ⟨idp, ih⟩,
  exact ⟨idp, ih⟩, exact ⟨idp, ih⟩, exact ⟨idp, ih⟩
end  

@[hott]
protected def ppred {sign : fo_signature} (form₀ : formula sign) : 
  ppred form₀ :=
  ppred.mk (λ form, formula.code form₀ form) (formula.refl form₀) 

@[hott, hsimp]
protected def decode {sign : fo_signature} : 
  Π {form₁ form₂ : formula sign}, formula.code form₁ form₂ -> form₁ = form₂ :=
begin
  intro form₁, hinduction form₁ with t₁ t₂ p r comp f₁ f₂ ih₁ ih₂ f₁ f₂ ih₁ ih₂
                                     f₁ f₂ ih₁ ih₂ f ih x f ih x f ih i f ih i f ih, 
  all_goals { intro form₂, 
              hinduction form₂ with t₁' t₂' p' r' comp' f₁' f₂' ih₁' ih₂' f₁' f₂' ih₁' ih₂'
                f₁' f₂' ih₁' ih₂' f' ih' x' f' ih' x' f' ih' i' f' ih' i' f' ih' }, 
  all_goals { intro code, try { hinduction code } }, 
  { fapply apd001, assumption, assumption, apply pathover_of_eq_tr, exact is_prop.elim _ _ },
  { exact apd011 formula.rel_terms fst snd },
  refl, refl,
  { exact ap011 formula.conj (ih₁ fst) (ih₂ snd) },
  { exact ap011 formula.disj (ih₁ fst) (ih₂ snd) },
  { exact ap011 formula.impl (ih₁ fst) (ih₂ snd) }, 
  { exact ap formula.neg (ih (code_neg_form f f' code)) }, 
  { exact ap011 formula.ex fst (ih snd) },
  { exact ap011 formula.univ fst (ih snd) }, 
  { fapply apd011 (@formula.inf_conj sign), exact fst, apply pathover_of_tr_eq, 
    apply eq_of_homotopy, intro j', exact (tr_dep_fn_eval_tr fst j') ⬝ (ih (fst⁻¹ ▸ j') 
               (snd (fst⁻¹ ▸ j'))) ⬝ (ap f' (@tr_inv_tr _ (λ i, sign.I i) _ _ fst j')) },
  { fapply apd011 (@formula.inf_disj sign), exact fst, apply pathover_of_tr_eq, 
    apply eq_of_homotopy, intro j', exact (tr_dep_fn_eval_tr fst j') ⬝ (ih (fst⁻¹ ▸ j') 
               (snd (fst⁻¹ ▸ j'))) ⬝ (ap f' (@tr_inv_tr _ (λ i, sign.I i) _ _ fst j')) }                          
end

@[hott]
def form_eq_equiv_code {sign : fo_signature} (form₀ : formula sign) :
  Π (form: formula sign), 
                  (form₀ = form) ≃ (formula.code form₀ form) :=
begin
  apply tot_space_contr_ppmap_id_eqv' _ (can_ppmap (formula.ppred form₀)), 
  fapply is_contr.mk, exact ⟨form₀, formula.refl form₀⟩, 
  intro f, hinduction f with form form_code, 
  change formula.code form₀ form at form_code,
  fapply sigma.sigma_eq,
  { exact formula.decode form_code },
  { apply pathover_of_tr_eq, change _ = form_code, 
    exact is_prop.elim _ _ }
end                   

@[hott, instance]
def form_is_set {sign : fo_signature} : is_set (formula sign) :=
begin
  apply is_trunc_succ_intro, intros form₁ form₂, 
  exact is_trunc_equiv_closed_rev -1 (form_eq_equiv_code form₁ form₂) 
                                     (formula.code_is_prop _ _)
end 

/- We use the class mechanism to implement the hierarchy of fragments in the first-order
   language given by the signature. -/
@[hott]
protected def atomic {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin hinduction φ, exact True, exact True, all_goals {exact False} end

@[hott]
class is_atomic {sign : fo_signature} (φ : formula sign) :=
  (atom : formula.atomic φ)

@[hott, instance]
def is_atomic_is_prop {sign : fo_signature} (φ : formula sign) : is_prop (is_atomic φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with a₁, hinduction φ₂ with a₂, 
  apply ap is_atomic.mk, exact is_prop.elim _ _
end

@[hott]
protected def horn {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact False, exact ih_a and ih_a_1, 
  all_goals {exact False} 
end

@[hott]
class is_horn {sign : fo_signature} (φ : formula sign) :=
  (horn : formula.horn φ)

@[hott, instance]
def is_horn_is_prop {sign : fo_signature} (φ : formula sign) : is_prop (is_horn φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with h₁, hinduction φ₂ with h₂, 
  apply ap is_horn.mk, exact is_prop.elim _ _
end

@[hott]
def atomic_implies_horn {sign : fo_signature} (φ : formula sign) : 
  formula.atomic φ -> formula.horn φ :=
begin hinduction φ, all_goals { intro a; try { exact a }; hinduction a } end  

@[hott, instance]
def atomic.to_horn {sign : fo_signature} (φ : formula sign) [H : is_atomic φ] : is_horn φ :=
  begin apply is_horn.mk, exact atomic_implies_horn φ H.atom end  

@[hott]
protected def regular {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact False, exact ih_a and ih_a_1, 
  exact False, exact False, exact False, exact ih, all_goals {exact False} 
end

@[hott]
class is_regular {sign : fo_signature} (φ : formula sign) :=
  (reg : formula.regular φ)

@[hott, instance]
def is_regular_is_prop {sign : fo_signature} (φ : formula sign) : is_prop (is_regular φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with r₁, hinduction φ₂ with r₂, 
  apply ap is_regular.mk, exact is_prop.elim _ _
end  

@[hott]
def horn_implies_regular {sign : fo_signature} (φ : formula sign) : 
  formula.horn φ -> formula.regular φ :=
begin 
  hinduction φ, all_goals { intro h }, exact h, exact h, exact h, exact h, 
  exact ⟨(ih_a h.1), (ih_a_1 h.2)⟩, all_goals { hinduction h } 
end  

@[hott, instance]
def horn.to_regular {sign : fo_signature} (φ : formula sign) [H : is_horn φ] : is_regular φ :=
  begin apply is_regular.mk, exact horn_implies_regular φ H.horn end

@[hott]
protected def coherent {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact True, exact ih_a and ih_a_1, 
  exact ih_a and ih_a_1, exact False, exact False, exact ih, all_goals {exact False} 
end

@[hott]
class is_coherent {sign : fo_signature} (φ : formula sign) :=
  (coh : formula.coherent φ)

@[hott, instance]
def is_coherent_is_prop {sign : fo_signature} (φ : formula sign) : is_prop (is_coherent φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with c₁, hinduction φ₂ with c₂, 
  apply ap is_coherent.mk, exact is_prop.elim _ _
end

@[hott]
def regular_implies_coherent {sign : fo_signature} (φ : formula sign) : 
  formula.regular φ -> formula.coherent φ :=
begin 
  hinduction φ, all_goals { intro r }, exact r, exact r, exact r, hinduction r, 
  exact ⟨(ih_a r.1), (ih_a_1 r.2)⟩, hinduction r, hinduction r, 
  hinduction r, exact ih r, all_goals { hinduction r } 
end  

@[hott, instance]
def regular.to_coherent {sign : fo_signature} (φ : formula sign) [H : is_regular φ] : 
  is_coherent φ :=
begin apply is_coherent.mk, exact regular_implies_coherent φ H.reg end  

@[hott]
protected def first_order {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact True, exact ih_a and ih_a_1, 
  exact ih_a and ih_a_1, exact ih_a and ih_a_1, exact ih, exact ih, exact ih, 
  all_goals {exact False} 
end

@[hott]
class is_first_order {sign : fo_signature} (φ : formula sign) :=
  (fo : formula.first_order φ)

@[hott, instance]
def is_firts_order_is_prop {sign : fo_signature} (φ : formula sign) : 
  is_prop (is_first_order φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with fo₁, hinduction φ₂ with fo₂, 
  apply ap is_first_order.mk, exact is_prop.elim _ _
end

@[hott]
def coherent_implies_first_order {sign : fo_signature} (φ : formula sign) : 
  formula.coherent φ -> formula.first_order φ :=
begin 
  hinduction φ, all_goals { intro c }, exact c, exact c, exact c, exact c, 
  exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, hinduction c,
  hinduction c, exact ih c, all_goals { hinduction c } 
end  

@[hott, instance]
def coherent.to_first_order {sign : fo_signature} (φ : formula sign) [H : is_coherent φ] : 
  is_first_order φ :=
begin apply is_first_order.mk, exact coherent_implies_first_order φ H.coh end

@[hott]
protected def geometric {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact True, exact ih_a and ih_a_1, 
  exact ih_a and ih_a_1, exact False, exact False, exact ih, exact False, exact False, 
  exact inf_conj ih 
end

@[hott]
class is_geometric {sign : fo_signature} (φ : formula sign) :=
  (geom : formula.geometric φ)

@[hott, instance]
def is_geometric_is_prop {sign : fo_signature} (φ : formula sign) : 
  is_prop (is_geometric φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with g₁, hinduction φ₂ with g₂, 
  apply ap is_geometric.mk, exact is_prop.elim _ _
end

@[hott]
def coherent_implies_geometric {sign : fo_signature} (φ : formula sign) : 
  formula.coherent φ -> formula.geometric φ :=
begin 
  hinduction φ, all_goals { intro c }, exact c, exact c, exact c, exact c, 
  exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, hinduction c,
  hinduction c, exact ih c, all_goals { hinduction c } 
end   

@[hott, instance]
def coherent.to_geometric {sign : fo_signature} (φ : formula sign) [H : is_coherent φ] : 
  is_geometric φ :=
begin apply is_geometric.mk, exact coherent_implies_geometric φ H.coh end

/- Infinitary first-order formulas are just formulas and don't need a separate label. -/


@[hott]
protected def free_vars {sign : fo_signature} : 
  formula sign -> dec_Subset (to_Set (var sign.labels sign.sorts)) :=
begin 
  intro form, hinduction form, 
  exact (free_vars_of_term t₁) ∪ (free_vars_of_term t₂), 
  exact iUnion (λ (k : sign.rels_arity r), free_vars_of_term ⟨sign.rels_comp k, comp k⟩),
  exact empty_Subset _, exact empty_Subset _, 
  exact subset.union ih_a ih_a_1, exact subset.union ih_a ih_a_1, 
  exact subset.union ih_a ih_a_1, exact ih, exact setminus ih (singleton_sset a),
  exact setminus ih (singleton_sset a), exact iUnion ih, exact iUnion ih
end

@[hott]
structure context_of {sign : fo_signature} (φ : formula sign) :=
  (cont : context sign)
  (in_cont : formula.free_vars φ ⊆ cont.vars)

@[hott]
structure formula_in_context (sign : fo_signature) := 
  (φ : formula sign) 
  (cont_of_φ : context_of φ)

@[hott]
def form_ext_cont {sign : fo_signature} {cont cont': context sign} 
  (inc_cont : cont.vars ⊆ cont'.vars) : 
  Π (φc : formula_in_context sign), (φc.cont_of_φ.1 = cont) -> formula_in_context sign :=
begin 
  intros φc p_cont, hinduction φc with φ φ_cont, 
  fapply formula_in_context.mk, exact φ, fapply context_of.mk, exact cont', 
  apply subset_trans _ _ _ φ_cont.2, change φ_cont.1 = cont at p_cont, 
  rwr p_cont, exact inc_cont 
end

@[hott]
def formula_in_context_eq {sign : fo_signature} {φc₁ φc₂ : formula_in_context sign} : 
  φc₁.φ = φc₂.φ -> φc₁.cont_of_φ.1 = φc₂.cont_of_φ.1 -> φc₁ = φc₂ :=
begin 
  intros pφ pc, hinduction φc₁ with φ φ_cont, hinduction φc₂ with φ' φ_cont',
  change φ = φ' at pφ, hinduction pφ, 
  fapply apd011 formula_in_context.mk idp,  
  apply pathover_of_tr_eq, rwr idp_tr, 
  hinduction φ_cont with cont in_cont, hinduction φ_cont' with cont' in_cont',
  fapply apd011 context_of.mk pc, apply pathover_of_tr_eq, exact is_prop.elim _ _ 
end   

@[hott]
def formula_in_context_eq_eta {sign : fo_signature}
  {φ₁ φ₂ : formula_in_context sign} (p : φ₁ = φ₂) : 
  formula_in_context_eq (ap formula_in_context.φ p) 
                        (ap (λ φ : formula_in_context sign, φ.cont_of_φ.cont) p) = p :=
begin 
  hinduction p, rwr ap_idp, rwr ap_idp, hinduction φ₁ with φ φ_cont,
  hinduction φ_cont with cont in_cont, 
  change apd011 formula_in_context.mk idp _ = _,  
  hsimp, exact idp 
end                 

@[hott, instance]
def formula_in_context_is_set {sign : fo_signature} :
  is_set (formula_in_context sign) :=
begin 
  apply is_set.mk, intros φ₁ φ₂ p q, 
  rwr <- formula_in_context_eq_eta p, rwr <- formula_in_context_eq_eta q,
    fapply apd011 formula_in_context_eq, exact is_set.elim _ _, 
  { apply pathover_of_tr_eq, exact is_set.elim _ _ } 
end

end formula


open formula  

@[hott]
structure sequent (sign : fo_signature) :=
  (ass : formula_in_context sign)
  (con : formula_in_context sign)

@[hott]
def seq_context {sign : fo_signature} (seq : sequent sign) : context sign := 
  context.mk (seq.ass.cont_of_φ.cont.vars ∪ seq.con.cont_of_φ.cont.vars)

@[hott]
def seq_cont_ass {sign : fo_signature} (seq : sequent sign) : formula_in_context sign :=
begin 
  fapply formula_in_context.mk, exact seq.ass.φ, 
  fapply context_of.mk, exact seq_context seq,
  exact subset_trans _ _ _ (formula.formula_in_context.cont_of_φ seq.ass).in_cont 
                           (union_sset_l _ _)
end

@[hott]
def seq_cont_con {sign : fo_signature} (seq : sequent sign) : formula_in_context sign :=
begin 
  fapply formula_in_context.mk, exact seq.con.φ, 
  fapply context_of.mk, exact seq_context seq,
  exact subset_trans _ _ _ (formula.formula_in_context.cont_of_φ seq.con).in_cont 
                           (union_sset_r _ _)
end

@[hott, hsimp]
def sequent_eq {sign : fo_signature} {seq₁ seq₂ : sequent sign} :
  Π (pa : seq₁.ass = seq₂.ass) (pc : seq₁.con = seq₂.con), seq₁ = seq₂ :=
begin 
  intros pa pc, 
  hinduction seq₁ with ass con, hinduction seq₂ with ass' con', 
  exact ap011 sequent.mk pa pc
end 

@[hott]
def sequent_eq_eta {sign : fo_signature} {seq₁ seq₂ : sequent sign} (p : seq₁ = seq₂) :
  sequent_eq (ap sequent.ass p) (ap sequent.con p) = p := 
begin hinduction p, hinduction seq₁, exact idp end 

@[hott, instance]
def sequent_is_set {sign : fo_signature} : is_set (sequent sign) :=
begin
  fapply is_set.mk, intros seq₁ seq₂ p q, 
  rwr <- sequent_eq_eta p, rwr <- sequent_eq_eta q,
  fapply ap011 sequent_eq, exact is_set.elim _ _, exact is_set.elim _ _
end 

/- We may need to introduce classes of sequents later on, if we need to invoke the class 
   mechanism. For now we just define the properties. -/

@[hott]
def sequent.horn {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.horn seq.ass.φ) and (formula.horn seq.con.φ) 

@[hott]
def sequent.regular {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.regular seq.ass.φ) and (formula.regular seq.con.φ) 

@[hott]
def sequent.coherent {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.coherent seq.ass.φ) and (formula.coherent seq.con.φ)  

@[hott]
def sequent.first_order {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.first_order seq.ass.φ) and (formula.first_order seq.con.φ)      

@[hott]
def sequent.geometric {sign : fo_signature} (seq : sequent sign) : trunctype.{0} -1 :=
  (formula.geometric seq.ass.φ) and (formula.geometric seq.con.φ) 

/- TODO : We need notations for formulas and sequents. -/

@[hott]
def fo_theory (sign : fo_signature) := Subset (to_Set (sequent sign)) 

namespace theory

/- To define modules and algebras we need two sorts in an otherwise algebraic theory. So we
   drop the requirement of only one sort in an algebraic theory. -/
@[hott]
class is_algebraic {sign : fo_signature} (th : fo_theory sign) :=
  (alg : prod (fin_Set 0 ≃ sign.rels) (Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (seq.ass.φ = formula.T sign) (formula.is_atomic seq.con.φ))))

@[hott, instance]
def is_algebraic_th.to_ass_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_algebraic th] (seq : to_Set (sequent sign)) (ax : seq ∈ th) : 
                                                  (formula.is_horn seq.ass.φ) :=
begin rwr (H.alg.2 seq ax).1, apply is_horn.mk, exact true.intro end

@[hott, instance]
def is_algebraic_th.to_con_is_atomic {sign : fo_signature} (th : fo_theory sign) 
  [H : is_algebraic th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_atomic seq.con.φ) :=
assume seq ax, (H.alg.2 seq ax).2  

@[hott]
class is_horn {sign : fo_signature} (th : fo_theory sign) :=
  (horn : Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (formula.is_horn seq.ass.φ) (formula.is_horn seq.con.φ)))

@[hott, instance]
def is_horn_th.to_ass_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_horn th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_horn seq.ass.φ) :=
assume seq ax, (@is_horn.horn _ _ H seq ax).1 

@[hott, instance]
def is_horn_th.to_con_is_horn {sign : fo_signature} (th : fo_theory sign) 
  [H : is_horn th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_horn seq.con.φ) :=
assume seq ax, (@is_horn.horn _ _ H seq ax).2 

@[hott, instance]
def algebraic_to_horn_theory {sign : fo_signature} (th : fo_theory sign) [is_algebraic th] : 
  is_horn th := 
begin 
  apply is_horn.mk, intros seq ax, fapply pair, 
  exact is_algebraic_th.to_ass_is_horn th seq ax, 
  exact @formula.atomic.to_horn _ _ (is_algebraic_th.to_con_is_atomic th seq ax)  
end

@[hott]
class is_regular {sign : fo_signature} (th : fo_theory sign) :=
  (reg : Π seq : to_Set (sequent sign), seq ∈ th -> 
                    (prod (formula.is_regular seq.ass.φ) (formula.is_regular seq.con.φ)))

@[hott, instance]
def is_reg_th.to_ass_is_reg {sign : fo_signature} (th : fo_theory sign) 
  [H : is_regular th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_regular seq.ass.φ) :=
assume seq ax, (@is_regular.reg _ _ H seq ax).1 

@[hott, instance]
def is_reg_th.to_con_is_reg {sign : fo_signature} (th : fo_theory sign) 
  [H : is_regular th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_regular seq.con.φ) :=
assume seq ax, (@is_regular.reg _ _ H seq ax).2 

@[hott, instance]
def horn_to_reg_theory {sign : fo_signature} (th : fo_theory sign) [is_horn th] : 
  is_regular th := 
begin 
  apply is_regular.mk, intros seq ax, fapply pair, 
  exact @formula.horn.to_regular _ _ (is_horn_th.to_ass_is_horn th seq ax),
  exact @formula.horn.to_regular _ _ (is_horn_th.to_con_is_horn th seq ax)  
end

@[hott]
class is_coherent {sign : fo_signature} (th : fo_theory sign) :=
  (coh : Π seq : to_Set (sequent sign), seq ∈ th -> 
                  (prod (formula.is_coherent seq.ass.φ) (formula.is_coherent seq.con.φ)))

@[hott, instance]
def is_coh_th.to_ass_is_coh {sign : fo_signature} (th : fo_theory sign) 
  [H : is_coherent th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_coherent seq.ass.φ) :=
assume seq ax, (@is_coherent.coh _ _ H seq ax).1 

@[hott, instance]
def is_coh_th.to_con_is_coh {sign : fo_signature} (th : fo_theory sign) 
  [H : is_coherent th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_coherent seq.con.φ) :=
assume seq ax, (@is_coherent.coh _ _ H seq ax).2 

@[hott, instance]
def reg_to_coh_theory {sign : fo_signature} (th : fo_theory sign) [is_regular th] : 
  is_coherent th := 
begin 
  apply is_coherent.mk, intros seq ax, fapply pair, 
  exact @formula.regular.to_coherent _ _ (is_reg_th.to_ass_is_reg th seq ax),
  exact @formula.regular.to_coherent _ _ (is_reg_th.to_con_is_reg th seq ax)  
end

@[hott]
class is_geometric {sign : fo_signature} (th : fo_theory sign) :=
  (geom : Π seq : to_Set (sequent sign), seq ∈ th -> 
                  (prod (formula.is_geometric seq.ass.φ) (formula.is_geometric seq.con.φ)))

@[hott, instance]
def is_geom_th.to_ass_is_geom {sign : fo_signature} (th : fo_theory sign) 
  [H : is_geometric th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_geometric seq.ass.φ) :=
assume seq ax, (@is_geometric.geom _ _ H seq ax).1 

@[hott, instance]
def is_geom_th.to_con_is_geom {sign : fo_signature} (th : fo_theory sign) 
  [H : is_geometric th] : Π seq : to_Set (sequent sign), seq ∈ th -> 
                                                  (formula.is_geometric seq.con.φ) :=
assume seq ax, (@is_geometric.geom _ _ H seq ax).2

@[hott, instance]
def coh_to_geom_theory {sign : fo_signature} (th : fo_theory sign) [is_coherent th] : 
  is_geometric th := 
begin 
  apply is_geometric.mk, intros seq ax, fapply pair, 
  exact @formula.coherent.to_geometric _ _ (is_coh_th.to_ass_is_coh th seq ax),
  exact @formula.coherent.to_geometric _ _ (is_coh_th.to_con_is_coh th seq ax)  
end

end theory

end signature

end hott