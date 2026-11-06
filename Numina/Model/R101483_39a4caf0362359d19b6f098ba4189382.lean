import Mathlib

open Real

theorem calculus_171954 (α : ℝ) (hα : α > 0) (F : ℝ → ℝ)
    (hF : ∀ x, x < 0 → F x = 0) (hF' : ∀ x, x ≥ 0 → F x = 1 - exp (-α * x)) :
    F = fun x => if x < 0 then 0 else 1 - exp (-α * x) := by
  funext x
  split_ifs with hx
  · -- Case where x < 0
    have h1 : F x = 0 := hF x hx
    exact h1
  · -- Case where x ≥ 0
    have h2 : F x = 1 - exp (-α * x) := hF' x (show x ≥ 0 by linarith)
    exact h2