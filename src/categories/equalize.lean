import categories.limits

universes v v' u u' w
hott_theory

namespace hott
open hott.eq hott.is_trunc hott.trunc hott.is_equiv hott.set hott.subset 
     hott.precategories hott.categories hott.categories.strict

namespace categories.limits

/- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` 
   with common domain and codomain. -/
@[hott, hsimp]
def parallel_pair_obj {C : Type _} [is_cat C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair -> C :=
λ s, match s with
     | wp_pair.up := a
     | wp_pair.down := b
     end    

@[hott, hsimp]
def parallel_pair_map {C : Type _} [is_cat C] {a b : C} 
  (f g : a ⟶ b) : Π {s t : walking_parallel_pair}, 
  (s ⟶ t) -> (parallel_pair_obj f g s ⟶ parallel_pair_obj f g t) :=
assume s t h, 
begin
  hinduction s, 
  { hinduction t,
    { exact 𝟙 a },
    { hinduction h,
      { exact f },
      { exact g } } },
  { hinduction t,
    { hinduction h },
    { exact 𝟙 b } }
end 

@[hott, hsimp]
def parallel_pair_map_id {C : Type _} [is_cat C] {a b : C} 
  (f g : a ⟶ b) : ∀ s : walking_parallel_pair, 
  parallel_pair_map f g (𝟙 s) = 𝟙 (parallel_pair_obj f g s) :=
by intro s; hinduction s; hsimp; hsimp   

@[hott, hsimp]
def parallel_pair_map_comp {C : Type _} [is_cat C] 
  {a b : C} (f g : a ⟶ b) : ∀ {s t u : walking_parallel_pair} 
  (h : s ⟶ t) (i : t ⟶ u), parallel_pair_map f g (h ≫ i) = 
                  (parallel_pair_map f g h) ≫ (parallel_pair_map f g i) :=
assume s t u h i,
begin
  hinduction s,
  { hinduction t,
    { hsimp },
    { hinduction u,
      { hinduction i },
      { rwr wpp_ci, hsimp } } },
  { hinduction t,
    { induction h },
    { hsimp } }
end  

@[hott]
def parallel_pair {C : Type _} [is_cat C] {a b : C} 
  (f g : a ⟶ b) : walking_parallel_pair ⥤ C :=
precategories.functor.mk (parallel_pair_obj f g) 
                           (@parallel_pair_map _ _ _ _ f g) 
                           (parallel_pair_map_id f g) 
                           (@parallel_pair_map_comp _ _ _ _ f g)   

/- A cone over a parallel pair is called a `fork`. -/
@[hott]
abbreviation fork {C : Type _} [is_cat C] {a b : C} (f g : a ⟶ b) := 
  @cone walking_parallel_pair _ _ _ (parallel_pair f g) 

@[hott] 
def fork_map {C : Type u} [is_cat.{v} C] {a b : C} {f g : a ⟶ b} (fk : fork f g) :
  ↥(fk.X ⟶ a) := fk.π.app wp_up

@[hott]
def fork_eq {C : Type u} [is_cat.{v} C] {a b : C} {f g : a ⟶ b} (fk : fork f g) :
  (fork_map fk) ≫ f = (fork_map fk) ≫ g :=
cone.fac fk wp_left ⬝ (cone.fac fk wp_right)⁻¹   
   
@[hott]
def fork.of_i {C : Type u} [is_cat.{v} C] {a b c : C} 
  {f g : a ⟶ b} (i : c ⟶ a) (w : i ≫ f = i ≫ g) : fork f g :=
have π : @constant_functor ↥walking_parallel_pair _ C _ c ⟹ parallel_pair f g, from
  let app :=  @wp_pair.rec (λ x, c ⟶ (parallel_pair f g).obj x) i (i ≫ f) in
  have naturality : ∀ (x x' : walking_parallel_pair) (h : x ⟶ x'), 
          ((@constant_functor ↥walking_parallel_pair _ C _ c).map h) ≫ (app x') = 
           (app x) ≫ ((parallel_pair f g).map h), from 
  begin
    intros x x' h, 
    hinduction x,
    { hinduction x',
      { hinduction h, hsimp },
      { hinduction h, 
        { hsimp, refl },
        { hsimp, exact w } } },  
    { hinduction x', 
      { hinduction h },
      { hinduction h, hsimp } }
  end,           
  nat_trans.mk app naturality,   
cone.mk c π 

@[hott]
def fork_of_i_is_fork {C : Type u} [is_cat.{v} C] {a b : C} {f g : a ⟶ b} (fk : fork f g) : 
  fork.of_i (fork_map fk) (fork_eq fk) = fk :=
begin
  hinduction fk, fapply apd011 cone.mk,
  { exact idp },
  { apply pathover_of_tr_eq, rwr idp_tr, apply nat_trans_eq,
    change @wp_pair.rec (λ x, X ⟶ (parallel_pair f g).obj x) _ _ = _,
    apply eq_of_homotopy, intro wpp, hinduction wpp, exact idp, 
    change π.app wp_up ≫ f = (cone.mk X π).π.app wp_down, 
    rwr <- cone.fac _ wp_left }
end

@[hott] 
def map_of_forks {C : Type u} [is_cat.{v} C] {a b : C} {f g : a ⟶ b} {fk₁ fk₂ : fork f g} :
  Π (vmap : fk₁.X ⟶ fk₂.X), vmap ≫ fork_map fk₂ = fork_map fk₁ -> cone_map fk₁ fk₂ :=
begin
  intros vmap eq, fapply cone_map.mk vmap,
  intro j, hinduction j,
  { exact eq },
  { change _ ≫ fk₂.π.app wp_down = fk₁.π.app wp_down, rwr <- cone.fac fk₂ wp_left, 
    rwr <- is_precat.assoc, change (_ ≫ fork_map fk₂) ≫ _ = _, rwr eq, exact cone.fac fk₁ _ } 
end

/- Limits of parallel pairs are `equalizers`. -/
@[hott]
class is_equalizer {C : Type u} [is_cat.{v} C] {a b : C} (f g : a ⟶ b) {c : C} (h : c ⟶ a) :=
  (eq : h ≫ f = h ≫ g)
  (limit : is_limit (fork.of_i h eq))

@[hott]
def fork_lift {C : Type u} [is_cat.{v} C] {a b c : C} {f g : a ⟶ b} (h : c ⟶ a) [H : is_equalizer f g h] 
  (fk : fork f g) : fk.X ⟶ c := 
(H.limit.lift fk).v_lift  

@[hott]
def fork_lift_eq {C : Type u} [is_cat.{v} C] {a b c : C} {f g : a ⟶ b} (h : c ⟶ a) [H : is_equalizer f g h] 
  (fk : fork f g) : fork_lift h fk ≫ h = fork_map fk :=
(H.limit.lift fk).fac wp_up

@[hott]
def fork_lift_uniq {C : Type u} [is_cat.{v} C] {a b c : C} {f g : a ⟶ b} {h : c ⟶ a} [H : is_equalizer f g h] 
  (fk : fork f g) (m : fk.X ⟶ c) : 
  m ≫ h = fork_map fk -> m = fork_lift h fk :=
begin 
  let equ_cone := fork.of_i h H.eq, 
  intro p,
  have m_fac : Π j : walking_parallel_pair, m ≫ equ_cone.π.app j = fk.π.app j, from 
  begin
    intro j, hinduction j, 
    { exact p }, 
    { change m ≫ equ_cone.π.app wp_down = fk.π.app wp_down,
      rwr <- cone.fac equ_cone wp_left, 
      rwr <- cone.fac fk wp_left, rwr <- is_precat.assoc m _ _, 
      change (m ≫ h) ≫ _ = _, rwr p }
  end,
  exact H.limit.uniq fk (cone_map.mk m m_fac),
end  

@[hott]
def fork_of_i_is_limit {C : Type u} [is_cat.{v} C] {a b c : C}  {f g : a ⟶ b} (i : c ⟶ a) (w : i ≫ f = i ≫ g)
  (fac : Π (fk : fork f g), Σ (h : fk.X ⟶ c), h ≫ i = fork_map fk) 
  (uniq : Π {fk : fork f g} (h₁ h₂ : fk.X ⟶ c) (eq₁ : h₁ ≫ i = fork_map fk) (eq₂ : h₂ ≫ i = fork_map fk), 
          h₁ = h₂) : is_limit (fork.of_i i w) :=
begin
  fapply is_limit.mk,
  { intro fk, fapply cone_map.mk,
    { exact (fac fk).1 },
    { intro j, hinduction j,
      { exact (fac fk).2 },
      { change _ ≫ (i ≫ f) = _, rwr <- is_precat.assoc, change _ = fk.π.app wp_down, 
        rwr <- cone.fac fk wp_left, exact ap (λ h, h ≫ f) (fac fk).2 } } },
  { intros fk m, fapply uniq,
    { exact m.fac wp_up },
    { exact (fac fk).2 } }
end

/- An equalizer is a subobject of the domain of the parallel pair. -/
@[hott]
def equalizer_as_subobject {C : Type u} [is_cat.{v} C] {a b c : C} (f g : a ⟶ b) (h : c ⟶ a)
  [H : is_equalizer f g h] : @subobject C _ a :=
begin
  fapply subobject.mk c h,
  { intros d e e' Hm, 
    have Hhe : (e ≫ h) ≫ f = (e ≫ h) ≫ g, from 
      (is_precat.assoc e h f) ⬝ ap (category_struct.comp e) H.eq ⬝ (is_precat.assoc e h g)⁻¹,
    have Hhf : e = fork_lift h (fork.of_i (e ≫ h) Hhe), from 
      fork_lift_uniq (fork.of_i (e ≫ h) Hhe) e rfl,  
    have Hh'e : (e' ≫ h) ≫ f = (e' ≫ h) ≫ g, from
      (is_precat.assoc e' h f) ⬝ ap (category_struct.comp e') H.eq ⬝ (is_precat.assoc e' h g)⁻¹,
    have Hh'f : e' = fork_lift h (fork.of_i (e' ≫ h) Hh'e), from 
      fork_lift_uniq (fork.of_i (e' ≫ h) Hh'e) e' rfl,
    rwr Hhf, rwr Hh'f, 
    let F : Π (h'': d ⟶ a), (h'' ≫ f = h'' ≫ g) -> (d ⟶ c) := 
                                                     (λ h'' p, fork_lift h (fork.of_i h'' p)),
    change F (e ≫ h) Hhe = F (e' ≫ h) Hh'e, fapply apd011 F, 
    exact Hm, apply pathover_of_tr_eq, exact is_set.elim _ _ }
end  

/- If `F : C ⥤ D` is a faithful functor, and if factorisation of a homomorphism in `D` underlying a homomorphism in `C`
   by a mono in `D` is underlying a homomorphism in `C`, then an object in `C` is an equalizer, if the underlying object 
   in `D` is an equalizer of the underlying homomorphisms. -/
@[hott]
def is_equalizer_to_is_equalizer {C : Type _} [is_cat C] {D : Type _} [is_cat D] (F : C ⥤ D) 
  (ffF : is_faithful_functor F) (mono_fac : Π {c₁ c₂ c : C} (f₁ : c₁ ⟶ c) (f₂ : c₂ ⟶ c) 
    (g : F.obj c₁ ⟶ F.obj c₂) (mon_F_f₂ : is_mono (F.map f₂)), g ≫ F.map f₂ = F.map f₁ -> Σ (h : c₁ ⟶ c₂), F.map h = g) :    
  Π {e c c' : C} (h₁ h₂ : c ⟶ c') (h : e ⟶ c), is_equalizer (F.map h₁) (F.map h₂) (F.map h) -> 
                                                 is_equalizer h₁ h₂ h :=
begin
  intros e c c' h₁ h₂ h equal, fapply is_equalizer.mk,
  { apply ffF, rwr functor.map_comp, rwr functor.map_comp, apply equal.eq },
  { fapply fork_of_i_is_limit,
    { intro fk, 
      have w : (F.map (fork_map fk)) ≫ (F.map h₁) = (F.map (fork_map fk)) ≫ (F.map h₂), from 
          begin rwr <- functor.map_comp, rwr <- functor.map_comp, rwr fork_eq end,
      let Ffk : fork (F.map h₁) (F.map h₂) := fork.of_i (F.map (fork_map fk)) w,
      let g : ↥(F.obj fk.X ⟶ F.obj e) := @fork_lift _ _ _ _ _ _ _ (F.map h) equal Ffk, 
      let Hso : @subobject D _ (F.obj c) := @equalizer_as_subobject _ _ _ _ _ (F.map h₁) (F.map h₂) (F.map h) equal,
      have Hm : is_mono (F.map h), from Hso.is_mono,
      have v : g ≫ F.map h = F.map (fork_map fk), from begin apply fork_lift_eq end,
      fapply sigma.mk,
      { exact (mono_fac (fork_map fk) h g Hm v).1 },
      { apply ffF, rwr functor.map_comp, 
        have p : F.map (mono_fac (fork_map fk) h g Hm v).fst = g, from (mono_fac (fork_map fk) h g Hm v).2,
        rwr p, exact v } },
    { intros fk g g' p p', apply ffF, 
      have w : (F.map (fork_map fk)) ≫ (F.map h₁) = (F.map (fork_map fk)) ≫ (F.map h₂), from 
          begin rwr <- functor.map_comp, rwr <- functor.map_comp, rwr fork_eq end,
      let Ffk : fork (F.map h₁) (F.map h₂) := fork.of_i (F.map (fork_map fk)) w,
      have Fp : F.map g ≫ F.map h = fork_map Ffk, from 
        begin rwr <- functor.map_comp, change (λ g, F.map g) (g ≫ h) = _, rwr ap (λ g, F.map g) p end,
      have Fp' : F.map g' ≫ F.map h = fork_map Ffk, from 
        begin rwr <- functor.map_comp, change (λ g, F.map g) (g' ≫ h) = _, rwr ap (λ g, F.map g) p' end,
      rwr @fork_lift_uniq _ _ _ _ _ _ _ _ equal Ffk (F.map g) Fp, 
      rwr @fork_lift_uniq _ _ _ _ _ _ _ _ equal Ffk (F.map g') Fp' } }  
end

@[hott]
class has_equalizer {C : Type u} [is_cat.{v} C] {a b : C} (f g : a ⟶ b) := 
  (has_limit : has_limit (parallel_pair f g))

@[hott, priority 100]
instance has_limit_of_has_equalizer {C : Type u} [is_cat.{v} C] {a b : C} (f g : a ⟶ b)
  [has_equalizer f g] : has_limit (parallel_pair f g) := 
has_equalizer.has_limit f g 

@[hott, instance]
def is_equalizer_of_has_equalizer {C : Type u} [is_cat.{v} C] {a b : C} (f g : a ⟶ b)
  [has_equalizer f g] : is_equalizer f g (fork_map (limit.cone (parallel_pair f g))) :=
begin
  fapply is_equalizer.mk, 
  { exact fork_eq (limit.cone (parallel_pair f g)) },
  { rwr fork_of_i_is_fork (limit.cone (parallel_pair f g)), exact limitcone_is_limit _ }
end

@[hott]
class has_equalizers (C : Type u) [is_cat.{v} C] := 
  (has_limit_of_shape : has_limits_of_shape walking_parallel_pair C)

@[hott, instance]
def has_equalizer_of_has_equalizers {C : Type u} [is_cat.{v} C] 
  [has_equalizers C] {a b : C} (f g : a ⟶ b) : has_equalizer f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ 
       (has_equalizers.has_limit_of_shape C) (parallel_pair f g)⟩

@[hott, instance]
def has_equalizer_of_has_limits_of_shape {C : Type u} [is_cat.{v} C] 
  [H : has_limits_of_shape walking_parallel_pair C] {a b : C} (f g : a ⟶ b) : 
  has_equalizer f g :=
⟨@has_limits_of_shape.has_limit _ _ _ _ H (parallel_pair f g)⟩ 

@[hott, instance]
def has_equalizers_of_has_limits (C : Type u) [is_cat.{v} C] [H : has_limits C] : 
  has_equalizers C :=
has_equalizers.mk (@has_limits.has_limit_of_shape C _ H walking_parallel_pair _)


end categories.limits

end hott
