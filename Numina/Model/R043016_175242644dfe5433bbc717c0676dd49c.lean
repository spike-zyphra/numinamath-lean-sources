import Mathlib

open Real

theorem algebra_316304 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (f : ℝ → ℝ)
    (hf : f = fun x => logb a (x + sqrt (1 + x ^ 2))) :
    Odd f := by
  use (fun x => (f x - 1) / 2 )
  funext x
  simp
  <;> ring_nf <;> field_simp <;> ring