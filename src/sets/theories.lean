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
   universe level to 1.
   
   We also need a restriction on contexts because too large sets of variables may not 
   allowed to be index sets of products in interpreting categories. -/
namespace signature

@[hott]
structure var (labels : Set.{0}) (sorts : Set.{0}) :=
  (label : labels)
  (sort : sorts) 

/- The following three lemmas should be produced automatically. -/
@[hott]
def var_eq {labels : Set.{0}} {sorts : Set.{0}} {v₁ v₂ : var labels sorts} : 
  (v₁.label = v₂.label) -> (v₁.sort = v₂.sort) -> (v₁ = v₂) :=
begin
  intros p_label p_sort, 
  hinduction v₁ with l₁ s₁, hinduction v₂ with l₂ s₂,
  exact ap011 var.mk p_label p_sort
end    

@[hott]
def var_eq_eta {labels : Set.{0}} {sorts : Set.{0}} {v₁ v₂ : var labels sorts} (p : v₁ = v₂) :
  var_eq (ap var.label p) (ap var.sort p) = p := 
begin hinduction p, hinduction v₁, reflexivity end    
    
@[hott, instance]
def var_is_set {labels : Set.{0}} {sorts : Set.{0}}  : is_set (var labels sorts) :=
begin
  fapply is_set.mk, intros x y p q, 
  rwr <- var_eq_eta p, rwr <- var_eq_eta q,
  apply ap011 var_eq, apply is_set.elim, apply is_set.elim
end   

@[hott]
structure fo_signature :=
  (sorts : Set.{0})
  (var_labels : Set.{0})
  (cont_pred : Subset (to_Set (var var_labels sorts)) -> trunctype.{0} -1)
                       -- This prescribes which sets of variables are allowed as contexts
  (ops : Set.{0}) 
  (ops_arity : Π (o : ops), Set.{0})
  (ops_source : Π (o : ops), ops_arity o -> sorts)
  (ops_target : Π (o : ops), sorts)
  (rels : Set.{0})
  (rels_arity : Π (r : rels), Set.{0})
  (rels_comp : Π {r : rels}, rels_arity r -> sorts)
  (I : Set.{0})
  (V : I -> Set.{0}) --sets over which infinite dis/conjunction can be taken, indexed by `I`

@[hott] 
inductive term_of_sort {sign : fo_signature} : sign.sorts -> Type
| var : Π (s : sign.sorts) (v : var sign.var_labels sign.sorts), (v.sort = s) -> 
                                                                          term_of_sort s
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
def free_vars_of_term {sign : fo_signature} : term sign -> 
  Subset (to_Set (var sign.var_labels sign.sorts)) :=
begin 
  intro t, hinduction t, hinduction term, 
  { exact elem_to_Subset v }, 
  { exact iUnion ih }
end


/- Terms and later formulas and sequents should always only contain free variables from a 
   `context`. -/
@[hott]
structure context (sign : fo_signature) := 
  (vars : Subset (to_Set (var sign.var_labels sign.sorts)))
  (pred : sign.cont_pred vars)

@[hott]
def context_eq {sign : fo_signature} {cont₁ cont₂ : context sign} : 
  (cont₁.vars = cont₂.vars) -> (cont₁ = cont₂) :=
begin
  intro p_vars, 
  hinduction cont₁ with vars₁ pred₁, hinduction cont₂ with vars₂ pred₂,
  apply apd011 context.mk p_vars, apply pathover_of_tr_eq, exact is_prop.elim _ _
end    

@[hott]
def context_eq_refl {sign : fo_signature} (cont : context sign) : 
  context_eq (@idp _ (cont.vars)) = (@idp _ cont) :=
begin 
  hinduction cont, hsimp, change apd011 context.mk (@idp _ vars) _ = _, 
  have H' : is_prop.elim ((@idp _ vars) ▸[λ v, sign.cont_pred v] pred) pred = idp, from 
    is_set.elim _ _,
  rwr H' 
end 

@[hott]
def context_eq_eta {sign : fo_signature} {cont₁ cont₂ : context sign} (p : cont₁ = cont₂) :
  context_eq (ap context.vars p) = p := 
begin hinduction p, hsimp, exact context_eq_refl cont₁ end 

@[hott, instance]
def context_is_set {sign : fo_signature} : is_set (context sign) :=
begin 
  fapply is_set.mk, intros x y p q, 
  rwr <- context_eq_eta p, rwr <- context_eq_eta q,
  apply ap context_eq, apply is_set.elim
end

@[hott]
structure term_in_context {sign : fo_signature} (cont : context sign) := 
  (t : term sign) 
  (in_cont : free_vars_of_term t ⊆ cont.vars)


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
| ex : var sign.var_labels sign.sorts -> formula -> formula 
| univ : var sign.var_labels sign.sorts -> formula -> formula 
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
def form_is_set {sign : fo_signature} : is_set (formula sign) :=
begin
  apply is_trunc_succ_intro, intros form₁ form₂,
  have eqv : (form₁ = form₂) ≃ (formula.code form₁ form₂), from 
    equiv.mk _ (tot_space_contr_id_equiv ⟨formula.code form₁, formula.refl form₁⟩ 
                                         (code_is_contr form₁) form₂), 
  exact is_trunc_equiv_closed_rev -1 eqv (code_is_prop _ _)
end 

/- We use the class mechanism to implement the hierarchy of fragments in the first-order
   language given by the signature. -/
@[hott]
protected def atomic {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin hinduction φ, exact True, exact True, all_goals {exact False} end

@[hott]
class is_atomic {sign : fo_signature} (φ : formula sign) :=
  (atom : formula.atomic φ)

@[hott]
protected def horn {sign : fo_signature} (φ : formula sign) : trunctype.{0} -1 :=
begin 
  hinduction φ, exact True, exact True, exact True, exact False, exact ih_a and ih_a_1, 
  all_goals {exact False} 
end

@[hott]
class is_horn {sign : fo_signature} (φ : formula sign) :=
  (horn : formula.horn φ)

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
  formula sign -> Subset (to_Set (var sign.var_labels sign.sorts)) :=
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
  (in_cont : formula.free_vars φ ⊆ cont.vars)

@[hott]
def formula_in_context_eq {sign : fo_signature} {cont : context sign} 
  {φ₁ φ₂ : formula_in_context cont} : 
  Π (p : φ₁.φ = φ₂.φ), φ₁.in_cont =[p; λ φ, formula.free_vars φ ⊆ cont.vars] φ₂.in_cont -> 
  φ₁ = φ₂ :=
begin intros, hinduction φ₁, hinduction φ₂, apply apdd _ p a end   

@[hott]
def formula_in_context_eq_eta {sign : fo_signature} {cont : context sign} 
  {φ₁ φ₂ : formula_in_context cont} (p : φ₁ = φ₂) : 
  formula_in_context_eq (ap formula_in_context.φ p) ((@apo01 _ _ 
     (λ f, formula.free_vars f⊆cont.vars) formula_in_context.φ (λ f, f.in_cont) _ _ p).1 
     (apd formula_in_context.in_cont p)) = p :=
begin hinduction p, hinduction φ₁, exact idp end                 

@[hott, instance]
def formula_in_context_is_set {sign : fo_signature} (cont : context sign) :
  is_set (formula_in_context cont) :=
begin 
  apply is_set.mk, intros φ₁ φ₂ p q, 
  rwr <- formula_in_context_eq_eta p, rwr <- formula_in_context_eq_eta q,
    fapply apd011 formula_in_context_eq, exact is_set.elim _ _, 
  { apply pathover_of_tr_eq, exact dep_set_eq_eq _ _ _ } end

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
begin intros, hinduction seq₁, hinduction seq₂, apply apdd2 sequent.mk p a a_1 end 

@[hott]
def sequent_eq_eta {sign : fo_signature} {seq₁ seq₂ : sequent sign} (p : seq₁ = seq₂) :
  sequent_eq (ap sequent.cont p) 
      ((apo01 sequent.cont (λ (a : sequent sign), a.ass) p).1 (apd sequent.ass p)) 
      ((apo01 sequent.cont (λ (a : sequent sign), a.con) p).1 (apd sequent.con p))  = p := 
begin hinduction p, hinduction seq₁, exact idp end 

@[hott, instance]
def sequent_is_set {sign : fo_signature} : is_set (sequent sign) :=
begin
  fapply is_set.mk, intros seq₁ seq₂ p q, 
  rwr <- sequent_eq_eta p, rwr <- sequent_eq_eta q,
  fapply apd0111 sequent_eq, exact is_set.elim _ _, 
  { apply pathover_of_tr_eq, exact dep_set_eq_eq _ _ _ }, 
  { apply pathover_of_tr_eq, exact dep_set_eq_eq _ _ _ }
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

/- We need notations for formulas and sequents. -/

@[hott]
def fo_theory (sign : fo_signature) := Subset (to_Set (sequent sign)) 

/- To define modules and algebras we need two sorts in an otherwise algebraic theory. So we
   drop the requirement of only one sort in an algebraic theory. -/
@[hott]
def theory.algebraic {sign : fo_signature} (th : fo_theory sign) : trunctype.{0} -1 :=
  prop_resize (to_Prop (Zero ≃ sign.rels) and 
              (to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (seq.ass.φ = formula.T sign) (formula.atomic seq.con.φ)))))

@[hott]
def theory.horn {sign : fo_signature} (th : fo_theory sign) : trunctype.{0} -1 :=
  prop_resize (to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (formula.horn seq.ass.φ) (formula.horn seq.con.φ))))

@[hott]
def theory.regular {sign : fo_signature} (th : fo_theory sign) : trunctype.{0} -1 :=
  prop_resize (to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (formula.regular seq.ass.φ) (formula.regular seq.con.φ))))

@[hott]
def theory.coherent {sign : fo_signature} (th : fo_theory sign) : trunctype.{0} -1 :=
  prop_resize (to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (formula.coherent seq.ass.φ) (formula.coherent seq.con.φ))))

@[hott]
def theory.geometric {sign : fo_signature} (th : fo_theory sign) : trunctype.{0} -1 :=
  prop_resize (to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> 
                        (prod (formula.geometric seq.ass.φ) (formula.geometric seq.con.φ))))

end signature

end hott