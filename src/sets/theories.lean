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
   
   We mainly follow the introduction to categorical model theory by [caramello14]. 

   First-order signatures prescribe the types of arguments and the arity of functions and 
   relations in a first-order theory. -/
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

namespace atomic

@[hott]
inductive atomic_formula (sign : fo_signature)
| eq_terms : Π (t₁ t₂ : term sign), (t₁.sort = t₂.sort) -> atomic_formula
| rel_terms : Π (r : sign.rels) 
       (comp : Π (k : sign.rels_arity r), term_of_sort (sign.rels_comp k)), atomic_formula

@[hott]
protected def code {sign : fo_signature} : 
  atomic_formula sign -> atomic_formula sign -> Type :=
begin
  intro atom₁, hinduction atom₁ with term₁ term₂ p,
  { intro atom₂, hinduction atom₂ with term₁' term₂' p', 
    { exact (term₁ = term₁') × (term₂ = term₂') },
    { exact Zero } },
  { intro atom₂, hinduction atom₂, 
    { exact Zero },
    { exact Σ (q : r = r_1), 
              comp =[q; λ s, Π (k : sign.rels_arity s), term_of_sort (sign.rels_comp k)] comp_1 } }
end  

@[hott, instance]
def code_is_prop  {sign : fo_signature} : 
  Π atom₁ atom₂ : atomic_formula sign, is_prop (atomic.code atom₁ atom₂) :=
begin
  intro atom₁, hinduction atom₁ with term₁ term₂ p, 
  { intro atom₂, hinduction atom₂ with term₁' term₂' p', 
    { apply is_prop.mk, intros q q', apply pair_eq, 
      exact is_prop.elim _ _, exact is_prop.elim _ _ },
    { apply is_prop.mk, intro q, hinduction q } },
  { intro atom₂, hinduction atom₂ with term₁' term₂' p', 
    { apply is_prop.mk, intro q, hinduction q },
    { apply is_prop.mk, intros code₁ code₂, 
      apply @sigma_Prop_eq (r = r_1) (λ q, to_Prop (comp =[q; λ s, Π (k : sign.rels_arity s), 
                                                    term_of_sort (sign.rels_comp k)] comp_1)),
      exact is_set.elim _ _ } }
end  

@[hott]
protected def refl {sign : fo_signature} : Π t : atomic_formula sign, atomic.code t t :=
  begin intro t, hinduction t, exact ⟨idp, idp⟩, exact ⟨idp, idpo⟩ end  

@[hott]
def encode {sign : fo_signature} {atom₁ atom₂ : atomic_formula sign} 
  (p : atom₁ = atom₂) : atomic.code atom₁ atom₂ :=
p ▸ (atomic.refl atom₁) 

@[hott, hsimp]
def decode {sign : fo_signature} : 
  Π {atom₁ atom₂ : atomic_formula sign}, atomic.code atom₁ atom₂ -> atom₁ = atom₂ :=
begin
  intro atom₁, hinduction atom₁,
  { intro atom₂, hinduction atom₂, 
    { intro atom_code, apply apd001 _ atom_code.1 atom_code.2, 
      apply pathover_of_tr_eq, exact is_prop.elim _ _ },
    { intro atom_code, hinduction atom_code } },
  { intro atom₂, hinduction atom₂, 
    { intro atom_code, hinduction atom_code },
    { intro atom_code, exact apd011 atomic_formula.rel_terms atom_code.1 atom_code.2 } }
end

@[hott]
def code_is_contr_to_refl {sign : fo_signature} (atom₁ : atomic_formula sign) : 
  Π (a_code : Σ (atom₂ : atomic_formula sign), atomic.code atom₁ atom₂), a_code = 
                                                           ⟨atom₁, atomic.refl atom₁⟩ :=
begin 
  intro a_code, fapply sigma.sigma_eq, 
  { exact (decode a_code.2)⁻¹ },
  { apply pathover_of_tr_eq, exact is_prop.elim _ _ } 
end

@[hott, instance]
def code_is_contr {sign : fo_signature} (atom₁ : atomic_formula sign) : 
  is_contr (Σ (atom₂ : atomic_formula sign), atomic.code atom₁ atom₂) :=
is_contr.mk _ (λ a_code, (code_is_contr_to_refl atom₁ a_code)⁻¹)  

@[hott, instance]
def atom_is_set {sign : fo_signature} : is_set (atomic_formula sign) :=
begin
  apply is_trunc_succ_intro, intros atom₁ atom₂,
  have eqv : (atom₁ = atom₂) ≃ (atomic.code atom₁ atom₂), from 
    equiv.mk _ (tot_space_contr_id_equiv ⟨atomic.code atom₁, atomic.refl atom₁⟩ 
                                         (code_is_contr atom₁) atom₂), 
  exact is_trunc_equiv_closed_rev -1 eqv (code_is_prop _ _)
end 

@[hott]
protected def free_vars {sign : fo_signature} : atomic_formula sign -> Subset (to_Set (var sign)) :=
begin 
  intro atom, hinduction atom, 
  { exact (free_vars_of_term t₁) ∪ (free_vars_of_term t₂) }, 
  { exact iUnion (λ (k : sign.rels_arity r), free_vars_of_term ⟨sign.rels_comp k, comp k⟩) } 
end

end atomic

open atomic

namespace formula

/- If we need more formation rules for formulas the definition has to be extended, together 
   with the proof that the type of formulas is a set and the association of free variables. -/
@[hott]
inductive formula (sign : fo_signature)   
| atom : atomic_formula sign -> formula
| T : formula

@[hott]
def free_vars {sign : fo_signature} : formula sign -> Subset (to_Set (var sign)) :=
begin 
  intro formula, hinduction formula, 
  { exact atomic.free_vars a },
  { exact empty_Subset _ }
end  

@[hott]
protected def code {sign : fo_signature} : 
  formula sign -> formula sign -> Type :=
begin
  intro form₁, hinduction form₁ with atom₁,
  { intro form₂, hinduction form₂ with atom₂, 
    { exact atom₁ = atom₂ },
    { exact Zero } },
  { intro form₂, hinduction form₂ with atom₂, 
    { exact Zero },
    { exact One } }
end  

@[hott, instance]
def code_is_prop  {sign : fo_signature} : 
  Π form₁ form₂ : formula sign, is_prop (formula.code form₁ form₂) :=
begin
  intro form₁, hinduction form₁ with atom₁, 
  { intro form₂, hinduction form₂ with atom₂, 
    { apply is_prop.mk, intros q q', exact is_set.elim _ _ },
    { apply is_prop.mk, intro q, hinduction q } },
  { intro atom₂, hinduction atom₂ with term₁' term₂' p', 
    { apply is_prop.mk, intro q, hinduction q },
    { apply is_prop.mk, intros code₁ code₂, exact @is_prop.elim _ One_is_prop _ _ } }
end 

@[hott]
protected def refl {sign : fo_signature} : Π t : formula sign, formula.code t t :=
  begin intro t, hinduction t, exact idp, exact One.star end  

@[hott, hsimp]
def decode {sign : fo_signature} : 
  Π {form₁ form₂ : formula sign}, formula.code form₁ form₂ -> form₁ = form₂ :=
begin
  intro form₁, hinduction form₁ with atom₁,
  { intro form₂, hinduction form₂ with atom₂, 
    { intro form_code, apply ap _ form_code },
    { intro form_code, hinduction form_code } },
  { intro form₂, hinduction form₂ with atom₂, 
    { intro form_code, hinduction form_code },
    { intro form_code, exact idp } }
end

@[hott]
def code_is_contr_to_refl {sign : fo_signature} (form₁ : formula sign) : 
  Π (f_code : Σ (form₂ : formula sign), formula.code form₁ form₂), f_code = 
                                                           ⟨form₁, formula.refl form₁⟩ :=
begin 
  intro f_code, fapply sigma.sigma_eq, 
  { exact (decode f_code.2)⁻¹ },
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

end formula

open formula

@[hott]
def context (sign : fo_signature) := Subset (to_Set (var sign))

@[hott, instance]
def context_is_set {sign : fo_signature} : is_set (context sign) :=
begin apply Powerset_is_set end

@[hott]
def term_in_context {sign : fo_signature} (t : term sign) 
  (cont : context sign) := (free_vars_of_term t) ⊆ cont

@[hott]
def formula_in_context {sign : fo_signature} (φ : formula sign) 
  (cont : context sign) := (free_vars φ) ⊆ cont  

@[hott]
structure sequent (sign : fo_signature) :=
  (cont : context sign)
  (ass : formula sign)
  (con : formula sign)
  (ass_in_cont : formula_in_context ass cont)
  (con_in_cont : formula_in_context con cont)

@[hott, hsimp]
def sequent_eq {sign : fo_signature} {seq₁ seq₂ : sequent sign} :
  (seq₁.cont = seq₂.cont) -> (seq₁.ass = seq₂.ass) -> (seq₁.con = seq₂.con) -> seq₁ = seq₂ :=
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

@[hott]
def fo_theory (sign : fo_signature) := Subset (to_Set (sequent sign)) 

@[hott]
def is_algebraic_seq {sign : fo_signature} : sequent sign -> Prop :=
begin
  intro seq, hinduction seq, hinduction ass with atom_ass,  
  { exact False }, --==assumption is True
  { hinduction con with atom_con, 
    { hinduction atom_con, exact True, exact False }, --conclusion is equality
    { exact False } }
end  

@[hott]
def is_algebraic {sign : fo_signature} : fo_theory sign -> Prop :=
  assume th, to_Prop (Π seq : to_Set (sequent sign), seq ∈ th -> is_algebraic_seq seq) and
             to_Prop (One ≃ sign.sorts) 

end signature

end hott
