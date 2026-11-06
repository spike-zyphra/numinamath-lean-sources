import Mathlib

theorem algebra_268700 {f g : ℝ → ℝ} (hfg : ∀ x, g (-x + 2) = f x - 1)
    (hf : ∀ x, f x = if x ∈ Set.Icc (-1) 0 then 2 * x + 2 else if x ∈ Set.Icc 0 2 then x / 2 + 2 else 0) :
    f = fun x => if x ∈ Set.Icc (-1) 0 then 2 * x + 2 else if x ∈ Set.Icc 0 2 then x / 2 + 2 else 0 := by
  funext x
  simpa using hf x