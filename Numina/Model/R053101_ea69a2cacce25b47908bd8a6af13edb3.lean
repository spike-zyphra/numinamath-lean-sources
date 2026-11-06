import Mathlib

theorem algebra_284487 (x y : ℝ) (h : y = 1.5 * x) :
    (x = 1 → y = 1.5) ∧ (x = 2 → y = 3) ∧ (x = 3 → y = 4.5) ∧ (x = 4 → y = 6) := by
  constructor
  · -- Assume x = 1, prove y = 1.5
    intro hx
    rw [hx] at h -- substitute x = 1 into h
    calc
      y = 1.5 * (1 : ℝ) := by rw [h]
      _ = 1.5 := by norm_num
  constructor
  · -- Assume x = 2, prove y = 3
    intro hx
    rw [hx] at h -- substitute x = 2 into h
    calc
      y = 1.5 * (2 : ℝ) := by rw [h]
      _ = 3 := by norm_num
  constructor
  · -- Assume x = 3, prove y = 4.5
    intro hx
    rw [hx] at h -- substitute x = 3 into h
    calc
      y = 1.5 * (3 : ℝ) := by rw [h]
      _ = 4.5 := by norm_num
  · -- Assume x = 4, prove y = 6
    intro hx
    rw [hx] at h -- substitute x = 4 into h
    calc
      y = 1.5 * (4 : ℝ) := by rw [h]
      _ = 6 := by norm_num