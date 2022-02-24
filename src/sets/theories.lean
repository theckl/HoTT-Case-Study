import sets.algebra init2 sets.axioms 

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
   universe level to 1.-/
namespace signature

@[hott]
structure fo_signature :=
  (sorts : Set.{0})
  (var_labels : Set.{0})
  (ops : Set.{0}) 
  (ops_arity : Π (o : ops), Set.{0})
  (ops_source : Π (o : ops), ops_arity o -> sorts)
  (ops_target : Π (o : ops), sorts)
  (rels : Set.{0})
  (rels_arity : Π (r : rels), Set.{0})
  (rels_comp : Π {r : rels}, rels_arity r -> sorts)
  (I : Set.{0})
  (V : I -> Set.{0})

@[hott]
structure var (sign : fo_signature) :=
  (label : sign.var_labels)
  (sort : sign.sorts) 

/- The following three lemmas should be produced automatically. -/
@[hott]
def var_eq {sign : fo_signature} {v₁ v₂ : var sign} : 
  (v₁.label = v₂.label) -> (v₁.sort = v₂.sort) -> (v₁ = v₂) :=
begin
  intros p_label p_sort, 
  hinduction v₁ with l₁ s₁, hinduction v₂ with l₂ s₂,
  exact ap011 var.mk p_label p_sort
end    

@[hott]
def var_eq_eta {sign : fo_signature} {v₁ v₂ : var sign} (p : v₁ = v₂) :
  var_eq (ap var.label p) (ap var.sort p) = p := 
begin hinduction p, hinduction v₁, reflexivity end    
    
@[hott, instance]
def var_is_set {sign : fo_signature} : is_set (var sign) :=
begin
  fapply is_set.mk, intros x y p q, 
  rwr <- var_eq_eta p, rwr <- var_eq_eta q,
  apply ap011 var_eq, apply is_set.elim, apply is_set.elim
end   

@[hott] 
inductive term_of_sort {sign : fo_signature} : sign.sorts -> Type
| var : Π (s : sign.sorts) (v : var sign), (v.sort = s) -> term_of_sort s
| op : Π (s : sign.sorts) (f : sign.ops) (p : sign.ops_target f = s)
         (args : Π (k : sign.ops_arity f), term_of_sort (sign.ops_source f k)), 
         term_of_sort s

namespace term

@[hott]
structure term (sign : fo_signature) :=
  (sort : sign.sorts)
  (term : term_of_sort sort)

@[hott]
def term_eq_sort {sign : fo_signature} {term₁ term₂ : term sign} :
  term₁ = term₂ -> term₁.sort = term₂.sort :=
assume p, ap term.sort p 

@[hott]
def term_eq_term {sign : fo_signature} {term₁ term₂ : term sign} :
  Π (q : term₁ = term₂), term₁.term =[term_eq_sort q] term₂.term :=
begin intro q, hinduction q, exact idpo end

@[hott]
protected def code {sign : fo_signature} : 
  term sign -> term sign -> Type :=
begin 
  intro term₁, hinduction term₁ with s₁ t₁, hinduction t₁, 
  { intro term₂, hinduction term₂ with s₂ t₂, hinduction t₂, 
    exact v = v_1, exact Zero },
  { intro term₂, hinduction term₂ with s₂ t₂, hinduction t₂, 
    { exact Zero }, 
    { exact Σ (q : f = f_1), Π k, ih k (⟨_, args_1 (q ▸ k)⟩) } } 
end

@[hott, instance]
def code_is_prop  {sign : fo_signature} : 
  Π term₁ term₂ : term sign, is_prop (term.code term₁ term₂) :=
begin
  intro term₁, hinduction term₁ with s₁ t₁, hinduction t₁ with s v p,  
  { intro term₂, hinduction term₂ with s₂ t₂, hinduction t₂ with s v' p', 
    { change is_prop (v = v'), apply is_prop.mk, intros q q', exact is_set.elim _ _ },
    { change is_prop Zero, apply_instance } },
  { intro term₂, hinduction term₂ with s₂ t₂, 
    hinduction t₂ with s v' p' s f' p' args' ih',
    { change is_prop Zero, apply_instance },
    { apply is_prop.mk, intros t₁_code t₂_code, fapply sigma.sigma_eq, 
      { exact is_set.elim _ _ },
      { apply pathover_of_tr_eq, apply tr_eq_of_eq_inv_tr, 
        apply eq_of_homotopy, intro k, exact @is_prop.elim _ (ih k _) _ _ } } }
end 

@[hott]
protected def refl {sign : fo_signature} : Π t : term sign, term.code t t :=
begin 
  intro term, hinduction term with s t, hinduction t,
  exact rfl , exact ⟨rfl, λ k, ih k⟩ 
end    

@[hott]
def encode {sign : fo_signature} {term₁ term₂ : term sign} 
  (p : term₁ = term₂) : term.code term₁ term₂ :=
p ▸ (term.refl term₁)  

@[hott, hsimp]
def decode {sign : fo_signature} : 
  Π {term₁ term₂ : term sign}, term.code term₁ term₂ -> term₁ = term₂ :=
begin
  intro term₁, hinduction term₁ with s₁ t₁, hinduction t₁, 
  { intro term₂, hinduction term₂ with s₂ t₂, hinduction t₂, 
    { intro t_code, 
      have q : v = v_1, from t_code, hinduction q, 
      have r : s = s_1, from a⁻¹ ⬝ a_1, hinduction r,
      fapply apd011 term.mk, exact rfl, apply pathover_idp_of_eq, 
      exact ap (term_of_sort.var s v) (is_set.elim _ _) },
    { intro t_code, hinduction t_code } },
  { intro term₂, hinduction term₂ with s₂ t₂, hinduction t₂,
    { intro t_code, hinduction t_code },
    { intro t_code, hinduction t_code with q args_code, hinduction q,
      have r : s = s_1, from p⁻¹ ⬝ p_1, hinduction r,
      have r' : p = p_1, from is_prop.elim _ _, hinduction r',      
      fapply apd011 term.mk, exact rfl, apply pathover_idp_of_eq,                 
      apply ap (term_of_sort.op s f p), apply eq_of_homotopy, intro k, hsimp,
      have q : term.mk _ (args k) = term.mk _ (args_1 k), from ih k (args_code k), 
      have p' : term_eq_sort q = idp, from is_set.elim _ _, 
      let q'' := term_eq_term q, rwr p' at q'', exact eq_of_pathover_idp q'' } }
end  

@[hott]
def code_is_contr_to_refl {sign : fo_signature} (term₁ : term sign) : 
  Π (t_code : Σ (term₂ : term sign), term.code term₁ term₂), t_code = 
                                                           ⟨term₁, term.refl term₁⟩ :=
begin 
  intro t_code, fapply sigma.sigma_eq, 
  { exact (decode t_code.2)⁻¹ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott, instance]
def code_is_contr {sign : fo_signature} (term₁ : term sign) : 
  is_contr (Σ (term₂ : term sign), term.code term₁ term₂) :=
is_contr.mk _ (λ t_code, (code_is_contr_to_refl term₁ t_code)⁻¹)  

@[hott, instance]
def term_is_set {sign : fo_signature} : is_set (term sign) :=
begin
  apply is_trunc_succ_intro, intros term₁ term₂,
  have eqv : (term₁ = term₂) ≃ (term.code term₁ term₂), from 
    equiv.mk _ (tot_space_contr_id_equiv ⟨term.code term₁, term.refl term₁⟩ 
                                         (code_is_contr term₁) term₂), 
  exact is_trunc_equiv_closed_rev -1 eqv (code_is_prop _ _)
end  

end term

open term

/- Terms of a specific sort also form a set. -/
@[hott]
def term_eq {sign : fo_signature} {term₁ term₂ : term sign} : 
  Π (p : term₁.sort = term₂.sort), (term₁.term =[p] term₂.term) -> (term₁ = term₂) :=
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
    { intro t, exact t.2 ▸ t.1.term },
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
def free_vars_of_term {sign : fo_signature} : term sign -> Subset (to_Set (var sign)) :=
begin 
  intro t, hinduction t, hinduction term, 
  { exact elem_to_Subset v }, 
  { exact iUnion ih }
end

/- Terms and later formulas and sequents should always only contain free variables from a 
   `context`. -/
@[hott]
def context (sign : fo_signature) := Subset (to_Set (var sign))

@[hott, instance]
def context_is_set {sign : fo_signature} : is_set (context sign) :=
begin apply Powerset_is_set end

@[hott]
structure term_in_context {sign : fo_signature} (cont : context sign) := 
  (t : term sign) 
  (in_cont : free_vars_of_term t ⊆ cont)

/- Formulas in the first-order language built upon a first-order signature, together with 
   the free variables that they contain, are defined inductively.   -/
namespace formula

@[hott]
inductive formula (sign : fo_signature)
| eq_terms : Π (t₁ t₂ : term sign), (t₁.sort = t₂.sort) -> formula
| rel_terms : Π (r : sign.rels) 
       (comp : Π (k : sign.rels_arity r), term_of_sort (sign.rels_comp k)), formula
| T : formula
| F : formula 
| conj : formula -> formula -> formula 
| disj : formula -> formula -> formula
| impl : formula -> formula -> formula 
| neg : formula -> formula
| ex : var sign -> formula -> formula 
| univ : var sign -> formula -> formula 
| inf_conj : Π (i : sign.I), (sign.V i -> formula) -> formula 
| inf_disj : Π (i : sign.I), (sign.V i -> formula) -> formula        

@[hott]
protected def code {sign : fo_signature} : formula sign -> formula sign -> Type :=
/- A match-expression does not work because we need proper induction. -/  
begin
  intro form₁, hinduction form₁ with t₁ t₂ p r comp f₁ f₁',
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --equality of terms
    all_goals { try { exact (t₁ = t₁') × (t₂ = t₂') } }, 
    all_goals { exact Zero } },
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --relations
    all_goals { try { exact Σ (q : r = r_1), 
      comp =[q; λ s, Π (k : sign.rels_arity s), term_of_sort (sign.rels_comp k)] comp_1 } }, 
    all_goals { exact Zero } },
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --T
    exact Zero, exact Zero, exact One, all_goals { exact Zero } },
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --F
    exact Zero, exact Zero, exact Zero, exact One, all_goals { exact Zero } }, 
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --conj
    exact Zero, exact Zero, exact Zero, exact Zero, exact prod (ih_a a) (ih_a_1 a_1),
    all_goals { exact Zero } },
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --disj
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, 
    exact prod (ih_a a_2) (ih_a_1 a_3), all_goals { exact Zero } },
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --impl
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
    exact prod (ih_a a_2) (ih_a_1 a_3), all_goals { exact Zero } },  
  { all_goals { intro form₂, hinduction form₂ with t₁' t₂' p' }, --neg
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
    exact ih a_1, all_goals { exact Zero } },
  { all_goals { intro form₂, hinduction form₂ }, --ex
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
    exact Zero, exact prod (a = a_2) (ih a_3), exact Zero, exact Zero, exact Zero },
  { all_goals { intro form₂, hinduction form₂ }, --univ
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
    exact Zero, exact Zero, exact prod (a = a_2) (ih a_3), exact Zero, exact Zero },  
  { all_goals { intro form₂, hinduction form₂ }, --inf_conj
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
    exact Zero, exact Zero, exact Zero, 
    exact Σ (q : i = i_1), Π v : sign.V i, ih v (a_1 (q ▸ v)), exact Zero },
  { all_goals { intro form₂, hinduction form₂ }, --inf_disj
    exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero, exact Zero,
    exact Zero, exact Zero, exact Zero, exact Zero, 
    exact Σ (q : i = i_1), Π v : sign.V i, ih v (a_1 (q ▸ v)) }   
end  

@[hott, instance]
def code_is_prop  {sign : fo_signature} : 
  Π form₁ form₂ : formula sign, is_prop (formula.code form₁ form₂) :=
begin
  intro form₁, hinduction form₁ with term₁ term₂ p, 
  all_goals { intro form₂, hinduction form₂ with term₁' term₂' p' },
  all_goals { try { exact Zero_is_prop } },
  all_goals { try { exact One_is_prop } }, 
  { apply is_prop.mk, intros q q', apply pair_eq, 
      exact is_prop.elim _ _, exact is_prop.elim _ _ }, 
  { apply is_prop.mk, intros code₁ code₂, 
    apply @sigma_Prop_eq (r = r_1) (λ q, to_Prop (comp =[q; λ s, Π (k : sign.rels_arity s), 
                                                    term_of_sort (sign.rels_comp k)] comp_1)),
    exact is_set.elim _ _ },
  all_goals { try { apply is_prop.mk, intros code₁ code₂, apply pair_eq, 
            exact @is_prop.elim _ (ih_a a_2) _ _, exact @is_prop.elim _ (ih_a_1 a_3) _ _ } },
  { apply is_prop.mk, intros code₁ code₂, exact @is_prop.elim _ (ih a_1) _ _ },
  all_goals { try { apply is_prop.mk, intros code₁ code₂, apply pair_eq, 
              exact is_prop.elim _ _, exact @is_prop.elim _ (ih a_3) _ _ } },
  all_goals { try { apply is_prop.mk, intros code₁ code₂, fapply sigma.sigma_eq, 
    exact is_prop.elim _ _ , apply pathover_of_tr_eq, apply eq_of_homotopy, intro v, 
    exact @is_prop.elim _ (ih v (a_1 (code₂.fst ▸[λ i, sign.V i] v))) _ (code₂.2 v) } }
end  

@[hott]
protected def refl {sign : fo_signature} : Π t : formula sign, formula.code t t :=
begin 
  intro t, hinduction t, exact ⟨idp, idp⟩, exact ⟨idp, idpo⟩, exact One.star, exact One.star,
  exact ⟨ih_a, ih_a_1⟩, exact ⟨ih_a, ih_a_1⟩, exact ⟨ih_a, ih_a_1⟩, exact ih, exact ⟨idp, ih⟩,
  exact ⟨idp, ih⟩, exact ⟨idp, ih⟩, exact ⟨idp, ih⟩
end  

@[hott]
def encode {sign : fo_signature} {form₁ form₂ : formula sign} (p : form₁ = form₂) : 
  formula.code form₁ form₂ := p ▸ (formula.refl form₁) 

@[hott, hsimp]
def decode {sign : fo_signature} : 
  Π {form₁ form₂ : formula sign}, formula.code form₁ form₂ -> form₁ = form₂ :=
begin
  intro form₁, hinduction form₁, 
  all_goals { intro form₂, hinduction form₂, all_goals { intro code, try { hinduction code } } }, 
  { fapply apd001, assumption, assumption, apply pathover_of_eq_tr, exact is_prop.elim _ _ },
  { exact apd011 formula.rel_terms fst snd },
  refl, refl,
  { exact ap011 formula.conj (ih_a fst) (ih_a_1 snd) },
  { exact ap011 formula.disj (ih_a fst) (ih_a_1 snd) },
  { exact ap011 formula.impl (ih_a fst) (ih_a_1 snd) }, 
  { exact ap formula.neg (ih code) }, 
  { exact ap011 formula.ex fst (ih snd) },
  { exact ap011 formula.univ fst (ih snd) }, 
  { fapply apd011 formula.inf_conj, exact fst, apply pathover_of_tr_eq, 
    apply eq_of_homotopy, intro v, exact (tr_dep_fn_eval_tr fst v) ⬝ (ih (fst⁻¹ ▸ v) 
                   (snd (fst⁻¹ ▸ v))) ⬝ (ap a_1 (@tr_inv_tr _ (λ i, sign.V i) _ _ fst v)) },
  { fapply apd011 formula.inf_disj, exact fst, apply pathover_of_tr_eq, 
    apply eq_of_homotopy, intro v, exact (tr_dep_fn_eval_tr fst v) ⬝ (ih (fst⁻¹ ▸ v) 
                   (snd (fst⁻¹ ▸ v))) ⬝ (ap a_1 (@tr_inv_tr _ (λ i, sign.V i) _ _ fst v)) }                          
end

@[hott]
def code_is_contr_to_refl {sign : fo_signature} (form₁ : formula sign) : 
  Π (f_code : Σ (form₂ : formula sign), formula.code form₁ form₂), f_code = 
                                                           ⟨form₁, formula.refl form₁⟩ :=
begin 
  intro a_code, fapply sigma.sigma_eq, 
  { exact (decode a_code.2)⁻¹ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott, instance]
def code_is_contr {sign : fo_signature} (form₁ : formula sign) : 
  is_contr (Σ (form₂ : formula sign), formula.code form₁ form₂) :=
is_contr.mk _ (λ f_code, (code_is_contr_to_refl form₁ f_code)⁻¹)  

@[hott, instance]
def atom_is_set {sign : fo_signature} : is_set (formula sign) :=
begin
  apply is_trunc_succ_intro, intros form₁ form₂,
  have eqv : (form₁ = form₂) ≃ (formula.code form₁ form₂), from 
    equiv.mk _ (tot_space_contr_id_equiv ⟨formula.code form₁, formula.refl form₁⟩ 
                                         (code_is_contr form₁) form₂), 
  exact is_trunc_equiv_closed_rev -1 eqv (code_is_prop _ _)
end 

@[hott]
protected def free_vars {sign : fo_signature} : formula sign -> Subset (to_Set (var sign)) :=
begin 
  intro form, hinduction form, 
  { exact (free_vars_of_term t₁) ∪ (free_vars_of_term t₂) }, 
  { exact iUnion (λ (k : sign.rels_arity r), free_vars_of_term ⟨sign.rels_comp k, comp k⟩) },
  exact empty_Subset _, exact empty_Subset _, 
  exact subset.union ih_a ih_a_1, exact subset.union ih_a ih_a_1, 
  exact subset.union ih_a ih_a_1, exact ih, exact setminus ih (elem_to_Subset a),
  exact setminus ih (elem_to_Subset a), exact iUnion ih, exact iUnion ih
end

@[hott]
structure formula_in_context {sign : fo_signature} (cont : context sign) := 
(φ : formula sign) 
(in_cont : formula.free_vars φ ⊆ cont)

end formula


open formula  

@[hott]
structure sequent (sign : fo_signature) :=
  (cont : context sign)
  (ass : formula_in_context cont)
  (con : formula_in_context cont)

@[hott, hsimp]
def sequent_eq {sign : fo_signature} {seq₁ seq₂ : sequent sign} :
  Π (p : seq₁.cont = seq₂.cont), seq₁.ass =[p] seq₂.ass -> seq₁.con =[p] seq₂.con -> 
                                                                         seq₁ = seq₂ :=
begin 
  intros, hinduction seq₁, hinduction seq₂, apply apd000011 sequent.mk a a_1 a_2, 
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end 

@[hott]
def sequent_eq_idp {sign : fo_signature} (seq : sequent sign) : 
  @sequent_eq _ seq seq idp idp idp = idp :=
begin hinduction seq, hsimp, rwr pathover_idp_of_id end  

@[hott]
def sequent_eq_eta {sign : fo_signature} {seq₁ seq₂ : sequent sign} (p : seq₁ = seq₂) :
  sequent_eq (ap sequent.cont p) (ap sequent.ass p) (ap sequent.con p) = p := 
begin hinduction p, hinduction seq₁, rwr ap_idp, rwr ap_idp, rwr ap_idp, rwr sequent_eq_idp _ end 

@[hott, instance]
def sequent_is_set {sign : fo_signature} : is_set (sequent sign) :=
begin
  fapply is_set.mk, intros seq₁ seq₂ p q, 
  rwr <- sequent_eq_eta p, rwr <- sequent_eq_eta q,
  apply eq.ap0111 sequent_eq, exact is_set.elim _ _, exact is_set.elim _ _, 
  exact is_set.elim _ _
end 

/- We need notations for formulas and sequents. -/

@[hott]
def fo_theory (sign : fo_signature) := Subset (to_Set (sequent sign)) 

@[hott]
def is_algebraic_form {sign : fo_signature} : formula sign -> Prop :=
begin
  intro form, hinduction form with atom T, 
  { hinduction atom with t₁ t₂ fun_eq rel, exact True, exact False }, --equality of terms
  { exact False }
end

@[hott]
def is_algebraic_seq {sign : fo_signature} : sequent sign -> Prop :=
begin
  intro seq, hinduction seq, hinduction ass with atom_ass,  
  { exact False }, --assumption is True
  { exact is_algebraic_form con } --conclusion is equality of terms
end  

@[hott]
def is_algebraic {sign : fo_signature} : fo_theory sign -> Prop :=
  assume th, to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> is_algebraic_seq seq) and
             to_Prop (One ≃ sign.sorts) 

end signature

end hott