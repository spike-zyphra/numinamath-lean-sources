import Mathlib

theorem algebra_215176 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n, a (n + 1) = a n / (2 * (n + 1) * a n + 1)) :
    ∑ k in Finset.Icc 1 2023, a k = 2023 / 2024 := by

  have h1 : ∀ n : ℕ, a (n + 1) = 1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by 
    intro n 
    induction n with 
    | zero =>
      rw [ha1]
      norm_num 
    | succ n ih =>
      have h2 := han (n + 1)
      rw [show n + 1 + 1 = n + 2 by omega] at h2 
      rw [h2] 
      rw [ih] 
      field_simp 
      <;> ring

  have h3 : ∀ k : ℕ, ∑ i in Finset.Icc 1 k, a i = 1 - 1 / (k + 1 : ℝ) := by
    intro k 
    induction k with 
    | zero =>
      norm_num
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      have h4 : a (k + 1) = 1 / ((k + 1 : ℝ) * (k + 2 : ℝ)) := h1 (k)
      simp [h4]
      field_simp 
      <;> ring

  have h4 : ∑ k in Finset.Icc 1 2023, a k = 1 - 1 / (2023 + 1 : ℝ) := by
    specialize h3 2023
    simpa using h3

  rw [h4]
  norm_num