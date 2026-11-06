import Mathlib

open Real Set
open scoped BigOperators

/-
Let $f\left(x\right)=e^{x}+ae^{-x}$, find a value of $a$ for which the statement "$f\left(x\right)$ is an increasing function on $R$" is true.
-/
theorem algebra_9234 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => exp x + a * exp (-x)) :
    a = -1 → (∀ x y, x < y → f x < f y) := by
  intro ha x y hxy
  simp_all
  -- By the strict monotonicity of exp function and x < y, we have exp x < exp y
  have h1 := exp_strictMono <| hxy
  -- Similarly, exp (-y) < exp (-x)
  have h2 := exp_strictMono <| neg_lt_neg hxy
  -- Therefore, by properties of inequalities, we get exp x - exp (-x) < exp y - exp (-y)
  -- Proof completed.
  linarith
