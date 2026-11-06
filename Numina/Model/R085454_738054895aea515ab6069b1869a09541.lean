import Mathlib

theorem algebra_97309 (f : ℝ → ℝ) (hf : f = fun x => (x + 1) / (x - 1)) :
    f (f (1 / 2)) ≠ 3 ∧ f (f (1 / 2)) ≠ -3 ∧ f (f (1 / 2)) ≠ 1 ∧ f (f (1 / 2)) ≠ -1 := by 
  have h1 : f (1 / 2) = -3 := by
    rw [hf]
    norm_num
  have h2 : f (f (1 / 2)) = 1 / 2 := by
    rw [h1]
    rw [hf]
    norm_num
  rw [h2]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num