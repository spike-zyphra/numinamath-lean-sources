import Mathlib

theorem algebra_103793 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x + b + 9 / x) :
    ∃ x0 ∈ Set.Icc 1 9, |f x0| ≥ 2 := by 
  by_contra h
  push_neg at h
  have h1 : ∀ x0, x0 ∈ Set.Icc 1 9 → |f x0| < 2 := by
    intro x0 hx0
    have h0 : |f x0| < 2 := by
      apply h x0
      simpa using hx0
    simpa using h0
  have h2 : |f 1| < 2 := h1 1 (by norm_num)
  have h3 : |f 3| < 2 := h1 3 (by norm_num)
  have h4 : |f 9| < 2 := h1 9 (by norm_num)
  have h11 : f 1 = a + b + 9 := by 
    rw [hf 1]
    norm_num
  have h33 : f 3 = 3 * a + b + 3 := by
    rw [hf 3]
    norm_num
    <;> linarith
  have h99 : f 9 = 9 * a + b + 1 := by 
    rw [hf 9]
    norm_num
    <;> linarith
  have h21 : -2 < f 1 := by linarith [abs_lt.mp h2]
  have h22 : f 1 < 2 := by linarith [abs_lt.mp h2]
  have h41 : -2 < f 3 := by linarith [abs_lt.mp h3]
  have h42 : f 3 < 2 := by linarith [abs_lt.mp h3]
  have h51 : -2 < f 9 := by linarith [abs_lt.mp h4]
  have h52 : f 9 < 2 := by linarith [abs_lt.mp h4]
  rw [h11] at h21 h22
  rw [h33] at h41 h42
  rw [h99] at h51 h52
  linarith