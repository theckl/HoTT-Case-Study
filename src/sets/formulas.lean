import sets.findecalg init2 sets.axioms sets.finite

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

end signature
open signature

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
  term_of_sort s₁ -> term_of_sort s₂ -> Two :=
begin
  intros s₁ s₂ t₁, revert s₂, 
  hinduction t₁ with s₁ x₁ px₁ s₁ o₁ pot₁ args₁ ih₁,
  all_goals { intros s₂ t₂, hinduction t₂ with s₂ x₂ px₂ s₂ o₂ pot₂ args₂ ih₂ },
  hinduction var_is_dec x₁ x₂, exact Two.one, exact Two.zero,
  exact Two.zero, exact Two.zero,
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
@[hott, reducible]
def free_vars (sign : fo_signature) := dec_Subset (to_Set (var sign.labels sign.sorts))

@[hott, instance]
def free_vars_is_set (sign : fo_signature) : is_set (free_vars sign) :=
  begin change is_set (dec_Subset _), exact dec_Powerset_is_set.{0 0} end

@[hott, reducible]
def no_FV (sign : fo_signature) : free_vars sign := 
  empty_dec_Subset (to_Set (var sign.labels sign.sorts))

@[hott, reducible]
def free_vars_of_term {sign : fo_signature} : term sign -> free_vars sign :=
begin 
  intro t, hinduction t, hinduction expr, 
  { exact singleton_dec_sset x }, 
  { exact ⋃ᵢ ih }
end

@[hott, instance]
def free_vars_of_term_is_fin {sign : fo_signature} (t : term sign) : 
  is_finite_dec_sset (free_vars_of_term t) :=
begin
  hinduction t, hinduction expr,
  { change ↥(to_Set (var sign.labels sign.sorts)) at x,
    exact singleton_dec_sset_fin.{0} x },
  { change is_finite_dec_sset (dec_fin_iUnion _), 
    apply dec_fin_union_fin, exact ih }
end


/- Formulas in the first-order language built upon a first-order signature, together with 
   the free variables that they contain, are defined as an inductive family, like 
   equality. This means that it is possible to set up the type of a formula with free 
   variables for which no witnesses can be constructed - as with equalities.   -/
namespace formula

@[hott]
inductive formula {sign : fo_signature} : free_vars sign -> Type 
| eq_terms : Π (t₁ t₂ : term sign), (t₁.sort = t₂.sort) -> 
                                formula (free_vars_of_term t₁ ∪ free_vars_of_term t₂)
| rel_terms : Π (r : sign.rels) (comp : Π (k : fin_Set (sign.rels_arity r)), 
                                          term_of_sort (sign.rels_comp k)), 
            formula (⋃ᵢ (λ k, free_vars_of_term (term.mk (sign.rels_comp k) (comp k))))
| T : formula (no_FV sign)
| F : formula (no_FV sign)
| conj {FV₁ FV₂ : free_vars sign}: (formula FV₁) -> (formula FV₂) -> (formula (FV₁ ∪ FV₂))
| disj {FV₁ FV₂ : free_vars sign}: (formula FV₁) -> (formula FV₂) -> (formula (FV₁ ∪ FV₂)) 
| impl {FV₁ FV₂ : free_vars sign}: (formula FV₁) -> (formula FV₂) -> (formula (FV₁ ∪ FV₂))
| neg {FV : free_vars sign} : (formula FV) -> (formula FV) 
| ex {FV : free_vars sign} : Π x : var sign.labels sign.sorts, formula FV -> 
                                        formula (dec_setminus FV (singleton_dec_sset x)) 
| univ {FV : free_vars sign} : Π x : var sign.labels sign.sorts, formula FV -> 
                                        formula (dec_setminus FV (singleton_dec_sset x)) 
| inf_conj : Π {I : sign.ind_Set} {FV : sign.I I -> free_vars sign} 
               (Hf : is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (FV i)))))
               (comp : Π {i : sign.I I}, formula (FV i)), formula (⋃ᵢ (λ i, FV i)) 
| inf_disj : Π {I : sign.ind_Set} {FV : sign.I I -> free_vars sign} 
               (Hf : is_finite (pred_Set (⋃ᵢ (λ i, dec_sset_to_sset (FV i)))))
               (comp : Π {i : sign.I I}, formula (FV i)), formula (⋃ᵢ (λ i, FV i))        

@[hott]
structure form_FV (sign : fo_signature) :=
  (FV : free_vars sign)
  (f : formula FV)

@[hott]
def form_FV_eq {sign : fo_signature} {fv₁ fv₂ : form_FV sign} :
  Π p : fv₁.FV = fv₂.FV, fv₁.f =[p] fv₂.f -> fv₁ = fv₂ :=
begin
  hinduction fv₁ with FV₁ f₁, hinduction fv₂ with FV₂ f₂,  
  intros p q, exact apd011 form_FV.mk p q
end

@[hott]
def form_FV_eq_form {sign : fo_signature} {fv₁ fv₂ : form_FV sign} : 
  Π p : fv₁ = fv₂, fv₁.f =[ap form_FV.FV p] fv₂.f :=
begin intro p, hinduction p, rwr ap_idp end   

@[hott]
def form_FV_eq_eq {sign : fo_signature} {fv₁ fv₂ : form_FV sign} :
  Π (p : fv₁ = fv₂), p = form_FV_eq (ap form_FV.FV p) (form_FV_eq_form p) :=
begin intro p, hinduction p, hinduction fv₁ with FV₁ f₁, refl end

@[hott]
def code_FV {sign : fo_signature} : form_FV sign -> form_FV sign -> Type :=
begin
  intro fv₁, hinduction fv₁ with FV₁ f₁,
  hinduction f₁ with t₁ t₂ p r comp FV₃ FV₄ f₁ f₂ ih₁ ih₂ FV₃ FV₄ f₁ f₂ ih₁ ih₂ FV₃ FV₄ 
                  f₁ f₂ ih₁ ih₂ FV f ih FV x f ih FV x f ih I j fin fI ih I j fin fI ih,
  all_goals { intro fv₂, hinduction fv₂ with FV₂ f₂,
    hinduction f₂ with t₁' t₂' p' r' comp' FV₃' FV₄' f₁' f₂' ih₁' ih₂' FV₃' FV₄' 
                                 f₁' f₂' ih₁' ih₂' FV₃' FV₄' f₁' f₂' ih₁' ih₂' FV' f' ih' 
                    FV' x' f' ih' FV' x' f' ih' I' j' fin' fI' ih' I' j' fin' fI' ih' },
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
  exact prod (ih₁ (form_FV.mk FV₃' f₁')) (ih₂ (form_FV.mk FV₄' f₂')), --conj
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact prod (ih₁ (form_FV.mk FV₃' f₁')) (ih₂ (form_FV.mk FV₄' f₂')), --disj
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact prod (ih₁ (form_FV.mk FV₃' f₁')) (ih₂ (form_FV.mk FV₄' f₂')), --impl
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
  exact ih (form_FV.mk FV' f'),  --neg
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact prod (x = x') (ih (form_FV.mk FV' f')),  --ex
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact prod (x = x') (ih (form_FV.mk FV' f')),  --univ
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,  
  exact Σ (p : I = I'), Π i : sign.I I, @ih i (form_FV.mk (j' (p ▸ i)) fI'), --inf_conj
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
  exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,  
  exact Σ (p : I = I'), Π i : sign.I I, @ih i (form_FV.mk (j' (p ▸ i)) fI') --inf_disj
end  

@[hott, hsimp]
protected def code {sign : fo_signature} {FV : free_vars sign} : 
  formula FV -> formula FV -> Type :=
λ f₁ f₂, code_FV (form_FV.mk FV f₁) (form_FV.mk FV f₂)
  
@[hott]
def code_neg_form {sign : fo_signature} {FV : free_vars sign} (f₁ f₂ : formula FV) : 
  formula.code (formula.neg f₁) (formula.neg f₂) -> formula.code f₁ f₂ := 
begin hsimp, intro c, exact c end

@[hott, instance]
def code_FV_is_prop  {sign : fo_signature} : 
  Π (fv₁ fv₂: form_FV sign), is_prop (code_FV fv₁ fv₂) :=
begin
  intro fv₁, hinduction fv₁ with FV₁ f₁, 
  hinduction f₁ with t₁ t₂ p r comp FV₃ FV₄ f₃ f₄ ih₁ ih₂ FV₃ FV₄ f₃ f₄ ih₁ ih₂
                               FV₃ FV₄ f₃ f₄ ih₁ ih₂ FV₃ f ih FV₃ x f ih FV₃ x f ih 
                               I j fin fI ih I j fin fI ih,
  all_goals { intro fv₂, hinduction fv₂ with FV₂ f₂,
            hinduction f₂ with t₁' t₂' p' r' comp' FV₃' FV₄' f₃' f₄' ih₁' ih₂' FV₃' FV₄'
                               f₃' f₄' ih₁' ih₂' FV₃' FV₄' f₃' f₄' ih₁' ih₂' FV₃' f' ih'
                    FV₃' x' f' ih' FV₃' x' f' ih' I' j' fin' fI' ih' I' j' fin' fI' ih' }, 
  all_goals { try { exact Zero_is_prop } },
  all_goals { try { exact One_is_prop } }, 
  { apply is_prop.mk, intros q q', apply pair_eq, 
      exact is_prop.elim _ _, exact is_prop.elim _ _ }, 
  { apply is_prop.mk, intros code₁ code₂, 
    apply @sigma_Prop_eq (r = r')
             (λ q, to_Prop (comp =[q; λ s, (Π (k : fin_Set (sign.rels_arity s)), 
                                              term_of_sort (sign.rels_comp k))] comp')),
    exact is_set.elim _ _ }, 
  all_goals { try { apply is_prop.mk, intros code₁ code₂, apply pair_eq, 
                    exact @is_prop.elim _ (ih₁ (form_FV.mk FV₃' f₃')) _ _, 
                    exact @is_prop.elim _ (ih₂ (form_FV.mk FV₄' f₄')) _ _ } },   
  { apply is_prop.mk, intros code₁ code₂, 
    exact @is_prop.elim _ (ih (form_FV.mk FV₃' f')) _ _ },
  all_goals { try { apply is_prop.mk, intros code₁ code₂, apply pair_eq, 
                    exact is_prop.elim _ _, 
                    exact @is_prop.elim _ (ih (form_FV.mk FV₃' f')) _ _ } },  
  all_goals { apply is_prop.mk, intros code₁ code₂, fapply sigma.sigma_eq, 
    exact is_prop.elim _ _ , apply pathover_of_tr_eq, apply eq_of_homotopy, intro i, 
    exact @is_prop.elim _ (@ih i (form_FV.mk (j' (code₂.1 ▸ i)) fI')) _ (code₂.2 i) }
end  

@[hott, instance]
protected def code_is_prop  {sign : fo_signature} {FV : free_vars sign} : 
  Π (f₁ f₂: formula FV), is_prop (formula.code f₁ f₂) :=
λ f₁ f₂, code_FV_is_prop (form_FV.mk FV f₁) (form_FV.mk FV f₂)

@[hott]
protected def refl {sign : fo_signature} {FV : free_vars sign} : 
  Π t : formula FV, formula.code t t :=
begin 
  intro t, hinduction t, exact ⟨idp, idp⟩, exact ⟨idp, idpo⟩, 
  exact One.star, exact One.star,
  exact ⟨ih_a, ih_a_1⟩, exact ⟨ih_a, ih_a_1⟩, exact ⟨ih_a, ih_a_1⟩,
  exact ih, exact ⟨idp, ih⟩,
  exact ⟨idp, ih⟩, exact ⟨idp, λ i, @ih i⟩, exact ⟨idp, λ i, @ih i⟩
end  

@[hott]
protected def ppred {sign : fo_signature} {FV : free_vars sign} (f₀ : formula FV) : 
  ppred f₀ :=
  ppred.mk (λ f, formula.code f₀ f) (formula.refl f₀) 

@[hott]
def form_FV_conj_eq {sign : fo_signature} {FV₁ FV₁' FV₂ FV₂' : free_vars sign} :
  Π {f₁ : formula FV₁} {f₁': formula FV₁'} {f₂ : formula FV₂} {f₂' : formula FV₂'},
    (form_FV.mk FV₁ f₁ = form_FV.mk FV₁' f₁') -> (form_FV.mk FV₂ f₂ = form_FV.mk FV₂' f₂') -> 
     form_FV.mk (FV₁ ∪ FV₂) (formula.conj f₁ f₂) = 
                                     form_FV.mk (FV₁' ∪ FV₂') (formula.conj f₁' f₂') :=
begin
  intros f₁ f₁' f₂ f₂' p₁ p₂,
  let q₁ : FV₁ = FV₁' := ap form_FV.FV p₁, let q₂ : FV₂ = FV₂' := ap form_FV.FV p₂,
  let q : FV₁ ∪ FV₂ = FV₁' ∪ FV₂' := q₂ ▸[λ FV, (FV₁ ∪ FV₂) = FV₁' ∪ FV] 
                              (q₁ ▸[λ FV, (FV₁ ∪ FV₂) = FV ∪ FV₂] idpath (FV₁ ∪ FV₂)),
  let r₁ : f₁ =[q₁] f₁' := pathover_ap formula form_FV.FV (apd form_FV.f p₁),
  let r₂ : f₂ =[q₂] f₂' := pathover_ap formula form_FV.FV (apd form_FV.f p₂),
  have r : formula.conj f₁ f₂ =[q; λ FV, formula FV] formula.conj f₁' f₂', from
    apdo01111' (λ FV₁ FV₂ : free_vars sign, FV₁ ∪ FV₂) 
        (λ (FV₁ FV₂ : free_vars sign) (f₁ : formula FV₁) (f₂ : formula FV₂), 
            formula.conj f₁ f₂) q₁ q₂ r₁ r₂,
  exact form_FV_eq q r
end

@[hott]
def form_FV_disj_eq {sign : fo_signature} {FV₁ FV₁' FV₂ FV₂' : free_vars sign} :
  Π {f₁ : formula FV₁} {f₁': formula FV₁'} {f₂ : formula FV₂} {f₂' : formula FV₂'},
    (form_FV.mk FV₁ f₁ = form_FV.mk FV₁' f₁') -> (form_FV.mk FV₂ f₂ = form_FV.mk FV₂' f₂') -> 
     form_FV.mk (FV₁ ∪ FV₂) (formula.disj f₁ f₂) = 
                                     form_FV.mk (FV₁' ∪ FV₂') (formula.disj f₁' f₂') :=
begin
  intros f₁ f₁' f₂ f₂' p₁ p₂,
  let q₁ : FV₁ = FV₁' := ap form_FV.FV p₁, let q₂ : FV₂ = FV₂' := ap form_FV.FV p₂,
  let q : FV₁ ∪ FV₂ = FV₁' ∪ FV₂' := q₂ ▸[λ FV, (FV₁ ∪ FV₂) = FV₁' ∪ FV] 
                              (q₁ ▸[λ FV, (FV₁ ∪ FV₂) = FV ∪ FV₂] idpath (FV₁ ∪ FV₂)),
  let r₁ : f₁ =[q₁] f₁' := pathover_ap formula form_FV.FV (apd form_FV.f p₁),
  let r₂ : f₂ =[q₂] f₂' := pathover_ap formula form_FV.FV (apd form_FV.f p₂),
  have r : formula.disj f₁ f₂ =[q; λ FV, formula FV] formula.disj f₁' f₂', from
    apdo01111' (λ FV₁ FV₂ : free_vars sign, FV₁ ∪ FV₂) 
        (λ (FV₁ FV₂ : free_vars sign) (f₁ : formula FV₁) (f₂ : formula FV₂), 
            formula.disj f₁ f₂) q₁ q₂ r₁ r₂,
  exact form_FV_eq q r
end

@[hott]
def form_FV_impl_eq {sign : fo_signature} {FV₁ FV₁' FV₂ FV₂' : free_vars sign} :
  Π {f₁ : formula FV₁} {f₁': formula FV₁'} {f₂ : formula FV₂} {f₂' : formula FV₂'},
    (form_FV.mk FV₁ f₁ = form_FV.mk FV₁' f₁') -> (form_FV.mk FV₂ f₂ = form_FV.mk FV₂' f₂') -> 
     form_FV.mk (FV₁ ∪ FV₂) (formula.impl f₁ f₂) = 
                                     form_FV.mk (FV₁' ∪ FV₂') (formula.impl f₁' f₂') :=
begin
  intros f₁ f₁' f₂ f₂' p₁ p₂,
  let q₁ : FV₁ = FV₁' := ap form_FV.FV p₁, let q₂ : FV₂ = FV₂' := ap form_FV.FV p₂,
  let q : FV₁ ∪ FV₂ = FV₁' ∪ FV₂' := q₂ ▸[λ FV, (FV₁ ∪ FV₂) = FV₁' ∪ FV] 
                              (q₁ ▸[λ FV, (FV₁ ∪ FV₂) = FV ∪ FV₂] idpath (FV₁ ∪ FV₂)),
  let r₁ : f₁ =[q₁] f₁' := pathover_ap formula form_FV.FV (apd form_FV.f p₁),
  let r₂ : f₂ =[q₂] f₂' := pathover_ap formula form_FV.FV (apd form_FV.f p₂),
  have r : formula.impl f₁ f₂ =[q; λ FV, formula FV] formula.impl f₁' f₂', from
    apdo01111' (λ FV₁ FV₂ : free_vars sign, FV₁ ∪ FV₂) 
        (λ (FV₁ FV₂ : free_vars sign) (f₁ : formula FV₁) (f₂ : formula FV₂), 
            formula.impl f₁ f₂) q₁ q₂ r₁ r₂,
  exact form_FV_eq q r
end

@[hott]
def form_FV_neg_eq {sign : fo_signature} {FV FV' : free_vars sign} :
  Π {f : formula FV} {f': formula FV'}, (form_FV.mk FV f = form_FV.mk FV' f') ->  
    form_FV.mk FV (formula.neg f) = form_FV.mk FV' (formula.neg f') :=
begin
  intros f f' p,
  let q : FV = FV' := ap form_FV.FV p,
  let r : f =[q] f' := pathover_ap formula form_FV.FV (apd form_FV.f p),
  have r_neg : formula.neg f =[q] formula.neg f', from apo _ r,
  exact form_FV_eq q r_neg
end

@[hott]
def form_FV_ex_eq {sign : fo_signature} {FV FV' : free_vars sign} :
  Π {f : formula FV} {f': formula FV'} {x x' : var sign.labels sign.sorts}, 
    (x = x') -> (form_FV.mk FV f = form_FV.mk FV' f') ->  
    form_FV.mk (dec_setminus FV (singleton_dec_sset x)) (formula.ex x f) = 
    form_FV.mk (dec_setminus FV' (singleton_dec_sset x')) (formula.ex x' f') :=
begin
  intros f f' x x' px p, hinduction px, 
  change ↥(to_Set (var sign.labels sign.sorts)) at x,
  let q := ap form_FV.FV p,
  let Fx := (λ vars, (dec_setminus vars (singleton_dec_sset x))),
  let qx : Fx FV = Fx FV' := ap Fx q,
  let r : f =[q] f' := pathover_ap formula form_FV.FV (apd form_FV.f p),
  have r_ex_p : formula.ex x f =[q; λ vars, formula (Fx vars)] formula.ex x f', from 
    apo _ r,
  have r_ex : formula.ex x f =[qx] formula.ex x f', from pathover_ap _ _ r_ex_p,
  exact form_FV_eq qx r_ex
end

@[hott]
def form_FV_univ_eq {sign : fo_signature} {FV FV' : free_vars sign} :
  Π {f : formula FV} {f': formula FV'} {x x' : var sign.labels sign.sorts}, 
    (x = x') -> (form_FV.mk FV f = form_FV.mk FV' f') ->  
    form_FV.mk (dec_setminus FV (singleton_dec_sset x)) (formula.univ x f) = 
    form_FV.mk (dec_setminus FV' (singleton_dec_sset x')) (formula.univ x' f') :=
begin
  intros f f' x x' px p, hinduction px, 
  change ↥(to_Set (var sign.labels sign.sorts)) at x,
  let q := ap form_FV.FV p,
  let Fx := (λ vars, (dec_setminus vars (singleton_dec_sset x))),
  let qx : Fx FV = Fx FV' := ap Fx q,
  let r : f =[q] f' := pathover_ap formula form_FV.FV (apd form_FV.f p),
  have r_univ_p : formula.univ x f =[q; λ vars, formula (Fx vars)] formula.univ x f', from 
    apo _ r,
  have r_univ : formula.univ x f =[qx] formula.univ x f', from pathover_ap _ _ r_univ_p,
  exact form_FV_eq qx r_univ
end

@[hott]
def form_FV_inf_conj_eq {sign : fo_signature} {I I' : sign.ind_Set}
  {j : (sign.I I) → free_vars sign} {j' : (sign.I I') → free_vars sign}
  {fin : is_finite (pred_Set (⋃ᵢλ i : sign.I I, dec_sset_to_sset (j i)))}
  {fin' : is_finite (pred_Set (⋃ᵢλ i', dec_sset_to_sset (j' i')))} :
  Π {fI : Π {i : sign.I I}, formula (j i)} {fI' : Π {i' : sign.I I'}, formula (j' i')}
    (p : I = I'), (Π (i : sign.I I), form_FV.mk (j i) (@fI i) = 
                                      form_FV.mk (j' (p ▸ i)) (@fI' (p ▸ i))) -> 
  form_FV.mk (⋃ᵢ (λ i, j i)) (formula.inf_conj fin @fI) =
                        form_FV.mk (⋃ᵢ (λ i', j' i')) (formula.inf_conj fin' @fI') :=
begin
  intros fI fI' p pI, 
  let qj : Π i, j i = j' (p ▸ i) := λ i, ap form_FV.FV (pI i), 
  have q : j =[p; λ I, sign.I I -> free_vars sign] j', from 
  begin 
    apply pathover_of_tr_eq, apply eq_of_homotopy, intro i', rwr tr_dep_fn_eval_tr, 
    rwr qj (p⁻¹ ▸ i'), rwr tr_inv_tr 
  end,
  have q' : Π (i : sign.I I), apo10_constant_right q i = qj i, from 
    assume i, is_set.elim _ _, 
  have r_fin : fin =[apd011 _ p q; id] fin', from 
    begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,
  have r_fam : @fI =[apd011 _ p q; id] @fI', from 
  begin
    apply deq_of_dep_homotopy2 p q @fI @fI', intro i, rwr q', 
    exact form_FV_eq_form (pI i)
  end, 
  let qI_dec : (⋃ᵢ (λ i, j i)) = (⋃ᵢ (λ i', j' i')) := apd01111_v2 _ p q r_fin r_fam,
  have r : formula.inf_conj fin @fI =[qI_dec] formula.inf_conj fin' @fI', from 
    begin exact apd01111_1 _ _ p q r_fin r_fam end,
  exact form_FV_eq qI_dec r
end

@[hott]
def form_FV_inf_disj_eq {sign : fo_signature} {I I' : sign.ind_Set}
  {j : (sign.I I) → free_vars sign} {j' : (sign.I I') → free_vars sign}
  {fin : is_finite (pred_Set (⋃ᵢλ i, dec_sset_to_sset (j i)))}
  {fin' : is_finite (pred_Set (⋃ᵢλ i', dec_sset_to_sset (j' i')))} :
  Π {fI : Π {i : sign.I I}, formula (j i)} {fI' : Π {i' : sign.I I'}, formula (j' i')}
    (p : I = I'), (Π (i : sign.I I), form_FV.mk (j i) (@fI i) = 
                                      form_FV.mk (j' (p ▸ i)) (@fI' (p ▸ i))) -> 
  form_FV.mk (⋃ᵢ (λ i, j i)) (formula.inf_disj fin @fI) =
                        form_FV.mk (⋃ᵢ (λ i', j' i')) (formula.inf_disj fin' @fI') :=
begin
  intros fI fI' p pI, 
  let qj : Π i, j i = j' (p ▸ i) := λ i, ap form_FV.FV (pI i), 
  have q : j =[p; λ I, sign.I I -> free_vars sign] j', from 
  begin 
    apply pathover_of_tr_eq, apply eq_of_homotopy, intro i', rwr tr_dep_fn_eval_tr, 
    rwr qj (p⁻¹ ▸ i'), rwr tr_inv_tr 
  end,
  have q' : Π (i : sign.I I), apo10_constant_right q i = qj i, from 
    assume i, is_set.elim _ _, 
  have r_fin : fin =[apd011 _ p q; id] fin', from 
    begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,
  have r_fam : @fI =[apd011 _ p q; id] @fI', from 
  begin
    apply deq_of_dep_homotopy2 p q @fI @fI', intro i, rwr q', 
    exact form_FV_eq_form (pI i)
  end, 
  let qI_dec : (⋃ᵢ (λ i, j i)) = (⋃ᵢ (λ i', j' i')) := apd01111_v2 _ p q r_fin r_fam,
  have r : formula.inf_disj fin @fI =[qI_dec] formula.inf_disj fin' @fI', from 
    begin exact apd01111_1 _ _ p q r_fin r_fam end,
  exact form_FV_eq qI_dec r
end

@[hott]
def decode_FV {sign : fo_signature} : 
  Π {fv₁ fv₂ : form_FV sign}, code_FV fv₁ fv₂ -> fv₁ = fv₂ :=
begin
  intro fv₁, hinduction fv₁ with FV₁ f₁, 
  hinduction f₁ with t₁ t₂ p r comp FV₃ FV₄ f₃ f₄ ih₁ ih₂ FV₃ FV₄ f₃ f₄ ih₁ ih₂
                               FV₃ FV₄ f₃ f₄ ih₁ ih₂ FV₃ f ih FV₃ x f ih FV₃ x f ih 
                               I j fin fI ih I j fin fI ih,
  all_goals { intro fv₂, hinduction fv₂ with FV₂ f₂,
            hinduction f₂ with t₁' t₂' p' r' comp' FV₃' FV₄' f₃' f₄' ih₁' ih₂' FV₃' FV₄'
                               f₃' f₄' ih₁' ih₂' FV₃' FV₄' f₃' f₄' ih₁' ih₂' FV₃' f' ih'
                    FV₃' x' f' ih' FV₃' x' f' ih' I' j' fin' fI' ih' I' j' fin' fI' ih' }, 
  all_goals { intro code },
  all_goals { try { solve1 { hinduction code } } },
  { hinduction code.1, hinduction code.2, hinduction is_set.elim p p', refl }, 
  { hinduction code with code_r code_c, hinduction code_r, 
    hinduction eq_of_pathover_idp code_c, refl },
  refl, refl, 
  { let p₁ := ih₁ code.1, let p₂ := ih₂ code.2, exact form_FV_conj_eq p₁ p₂ },
  { let p₁ := ih₁ code.1, let p₂ := ih₂ code.2, exact form_FV_disj_eq p₁ p₂ },
  { let p₁ := ih₁ code.1, let p₂ := ih₂ code.2, exact form_FV_impl_eq p₁ p₂ },
  { let p := ih code, exact form_FV_neg_eq p }, 
  { exact form_FV_ex_eq code.1 (ih code.2) },
  { exact form_FV_univ_eq code.1 (ih code.2) },
  { exact form_FV_inf_conj_eq code.1 
                          (λ i, @ih i (form_FV.mk (j' (code.1 ▸ i)) fI') (code.2 i)) },
  { exact form_FV_inf_disj_eq code.1 
                          (λ i, @ih i (form_FV.mk (j' (code.1 ▸ i)) fI') (code.2 i)) }
end 

@[hott, hsimp]
protected def decode {sign : fo_signature} {FV : free_vars sign} : 
  Π {f₁ f₂ : formula FV}, formula.code f₁ f₂ -> f₁ = f₂ :=
begin 
  intros f₁ f₂, hsimp, intro cFV, 
  have pfFV : (form_FV.mk FV f₁) = (form_FV.mk FV f₂), from decode_FV cFV,
  let pFV : FV = FV := ap form_FV.FV pfFV,
  have pFV_eq : pFV = idp, from 
    @is_set.elim (dec_Subset _) (@dec_Powerset_is_set.{0 0} _) _ _ _ _,
  have pf : pFV ▸ f₁ = f₂, from 
  begin 
    apply tr_eq_of_pathover, change (form_FV.mk FV f₁).f =[pFV] (form_FV.mk FV f₂).f,
    exact form_FV_eq_form _ 
  end,
  rwr pFV_eq at pf, rwr idp_tr at pf, exact pf 
end

@[hott]
def form_eq_equiv_code {sign : fo_signature} {FV : free_vars sign} (f₀ : formula FV) :
  Π (f: formula FV), (f₀ = f) ≃ (formula.code f₀ f) :=
begin
  apply tot_space_contr_ppmap_id_eqv' _ (can_ppmap (formula.ppred f₀)), 
  fapply is_contr.mk, exact ⟨f₀, formula.refl f₀⟩, 
  intro fpp, hinduction fpp with f f_code, 
  change formula.code f₀ f at f_code,
  fapply sigma.sigma_eq,
  { exact formula.decode f_code },
  { apply pathover_of_tr_eq, change _ = f_code, 
    exact is_prop.elim _ _ }
end                   

@[hott, instance]
def form_is_set {sign : fo_signature} {FV : free_vars sign} : is_set (formula FV) :=
begin
  apply is_trunc_succ_intro, intros form₁ form₂, 
  exact is_trunc_equiv_closed_rev -1 (form_eq_equiv_code form₁ form₂) 
                                     (formula.code_is_prop _ _)
end 

@[hott, instance]
def form_FV_is_set {sign : fo_signature} : is_set (form_FV sign) :=
begin
  fapply is_set.mk, intros fFV₁ fFV₂ p q, 
  hinduction fFV₁ with FV₁ f₁, hinduction fFV₂ with FV₂ f₂, 
  let pFV := ap form_FV.FV p, let qFV := ap form_FV.FV q,
  have rFV : pFV = qFV, from is_prop.elim _ _,
  let pf := form_FV_eq_form p,  
  let qf := form_FV_eq_form q, 
  have rf : pf =[rFV; λ r : FV₁ = FV₂, f₁ =[r] f₂] qf, from 
    begin apply pathover_of_tr_eq, exact is_prop.elim _ _ end,
  rwr form_FV_eq_eq p, rwr form_FV_eq_eq q,
  change form_FV_eq pFV pf = form_FV_eq qFV qf,
  fapply apd011 form_FV_eq, exact rFV, exact rf
end

/- We use the class mechanism to implement the hierarchy of fragments in the first-order
   language given by the signature. -/
@[hott]
protected def atomic {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  trunctype.{0} -1 :=
begin hinduction φ, exact True, exact True, all_goals {exact False} end

@[hott]
class is_atomic {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :=
  (atom : formula.atomic φ)

@[hott, instance]
def is_atomic_is_prop {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  is_prop (is_atomic φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with a₁, hinduction φ₂ with a₂, 
  apply ap is_atomic.mk, exact is_prop.elim _ _
end

@[hott]
protected def horn {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact False, exact ih_a and ih_a_1, 
  all_goals {exact False} 
end

@[hott]
class is_horn {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :=
  (horn : formula.horn φ)

@[hott, instance]
def is_horn_is_prop {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  is_prop (is_horn φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with h₁, hinduction φ₂ with h₂, 
  apply ap is_horn.mk, exact is_prop.elim _ _
end

@[hott]
def atomic_implies_horn {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  formula.atomic φ -> formula.horn φ :=
begin hinduction φ, all_goals { intro a; try { exact a }; hinduction a } end  

@[hott, instance]
def atomic.to_horn {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) 
  [H : is_atomic φ] : is_horn φ :=
begin apply is_horn.mk, exact atomic_implies_horn φ H.atom end  

@[hott]
protected def regular {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact False, exact ih_a and ih_a_1, 
  exact False, exact False, exact False, exact ih, all_goals {exact False} 
end

@[hott]
class is_regular {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :=
  (reg : formula.regular φ)

@[hott, instance]
def is_regular_is_prop {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  is_prop (is_regular φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with r₁, hinduction φ₂ with r₂, 
  apply ap is_regular.mk, exact is_prop.elim _ _
end  

@[hott]
def horn_implies_regular {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  formula.horn φ -> formula.regular φ :=
begin 
  hinduction φ, all_goals { intro h }, exact h, exact h, exact h, exact h, 
  exact ⟨(ih_a h.1), (ih_a_1 h.2)⟩, all_goals { hinduction h } 
end  

@[hott, instance]
def horn.to_regular {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) 
  [H : is_horn φ] : is_regular φ :=
begin apply is_regular.mk, exact horn_implies_regular φ H.horn end

@[hott]
protected def coherent {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact True, exact ih_a and ih_a_1, 
  exact ih_a and ih_a_1, exact False, exact False, exact ih, all_goals {exact False} 
end

@[hott]
class is_coherent {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :=
  (coh : formula.coherent φ)

@[hott, instance]
def is_coherent_is_prop {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  is_prop (is_coherent φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with c₁, hinduction φ₂ with c₂, 
  apply ap is_coherent.mk, exact is_prop.elim _ _
end

@[hott]
def regular_implies_coherent {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  formula.regular φ -> formula.coherent φ :=
begin 
  hinduction φ, all_goals { intro r }, exact r, exact r, exact r, hinduction r, 
  exact ⟨(ih_a r.1), (ih_a_1 r.2)⟩, hinduction r, hinduction r, 
  hinduction r, exact ih r, all_goals { hinduction r } 
end  

@[hott, instance]
def regular.to_coherent {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) 
  [H : is_regular φ] : is_coherent φ :=
begin apply is_coherent.mk, exact regular_implies_coherent φ H.reg end  

@[hott]
protected def first_order {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact True, exact ih_a and ih_a_1, 
  exact ih_a and ih_a_1, exact ih_a and ih_a_1, exact ih, exact ih, exact ih, 
  all_goals {exact False} 
end

@[hott]
class is_first_order {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :=
  (fo : formula.first_order φ)

@[hott, instance]
def is_first_order_is_prop {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  is_prop (is_first_order φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with fo₁, hinduction φ₂ with fo₂, 
  apply ap is_first_order.mk, exact is_prop.elim _ _
end

@[hott]
def coherent_implies_first_order {sign : fo_signature} {FV : free_vars sign}
  (φ : formula FV) : formula.coherent φ -> formula.first_order φ :=
begin 
  hinduction φ, all_goals { intro c }, exact c, exact c, exact c, exact c, 
  exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, hinduction c,
  hinduction c, exact ih c, all_goals { hinduction c } 
end  

@[hott, instance]
def coherent.to_first_order {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) 
  [H : is_coherent φ] : is_first_order φ :=
begin apply is_first_order.mk, exact coherent_implies_first_order φ H.coh end

@[hott]
protected def geometric {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact True, exact ih_a and ih_a_1, 
  exact ih_a and ih_a_1, exact False, exact False, exact ih, exact False, exact False, 
  exact inf_conj @ih 
end

@[hott]
class is_geometric {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) :=
  (geom : formula.geometric φ)

@[hott, instance]
def is_geometric_is_prop {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) : 
  is_prop (is_geometric φ) :=
begin
  apply is_prop.mk, intros φ₁ φ₂, hinduction φ₁ with g₁, hinduction φ₂ with g₂, 
  apply ap is_geometric.mk, exact is_prop.elim _ _
end

@[hott]
def coherent_implies_geometric {sign : fo_signature} {FV : free_vars sign} 
  (φ : formula FV) : formula.coherent φ -> formula.geometric φ :=
begin 
  hinduction φ, all_goals { intro c }, exact c, exact c, exact c, exact c, 
  exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, exact ⟨(ih_a c.1), (ih_a_1 c.2)⟩, hinduction c,
  hinduction c, exact ih c, all_goals { hinduction c } 
end   

@[hott, instance]
def coherent.to_geometric {sign : fo_signature} {FV : free_vars sign} (φ : formula FV) 
  [H : is_coherent φ] : is_geometric φ :=
begin apply is_geometric.mk, exact coherent_implies_geometric φ H.coh end

/- Infinitary first-order formulas are just formulas and don't need a separate label. -/

end formula

end hott