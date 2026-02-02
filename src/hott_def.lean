import hott.init

universes u u' v w
hott_theory

namespace hott

/- Should be in [init.function]. -/
@[inline, reducible] def function.comp {α β φ : Type _} (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

hott_theory_cmd "local infixr  ` ∘ `:80      := hott.function.comp"

/- Should be in [init.path]. -/
notation eq `▸[`:50 P:0 `]`:0 b:50 := transport P eq b 

@[hott, hsimp, reducible]
def id {A : Type _} (a : A) : A := a 

end hott