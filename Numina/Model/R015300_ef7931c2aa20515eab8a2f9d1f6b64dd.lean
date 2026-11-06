import Mathlib

theorem algebra_22189 (f : ℝ → ℝ) (c : ℝ) (hf : f = fun x => 4 * x ^ 7 + x ^ 5 + 3 * x ^ 2 - 2 * x + c) :
    f (-1) = 0 ↔ c = 0 := by 
  simp [hf]
  constructor
  · -- Assume  f(-1) = 0. We need to prove  c = 0.
    intro h
    norm_num at h 
    linarith
  · -- Assume c = 0. We need to prove f(-1) = 0
    intro h 
    rw [h] 
    norm_num