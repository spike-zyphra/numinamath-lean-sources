import Mathlib

theorem algebra_11851 {a b : ℕ → ℝ} (ha1 : a 1 = 1 / 4) (ha2 : a 2 = 3 / 4)
    (han : ∀ n ≥ 2, a (n + 1) = 2 * a n - a (n - 1)) (hb1 : b 1 ≠ 1 / 4)
    (hbn : ∀ n ≥ 2, 3 * b n - b (n - 1) = n) (hb1' : b 1 = 11 / 12) :
    ∑ i in Finset.Icc 1 n, b i = 1 / 4 * n ^ 2 - (1 / 3) ^ n + 1 := by

  have eq1 : ∀ (n : ℕ), b (n + 1) = 2 / 3 ^ (n + 1 : ℕ) + (1 / 2 : ℝ) * (n + 1 : ℕ) - 1 / 4 := by 
    intro n
    induction n with 
    | zero =>
      rw [hb1']
      norm_num 
    | succ n ih =>
      have eq2 : 3 * b (n + 2) - b (n + 1) = (n + 2 : ℝ) := by 
        specialize hbn (n + 2) (by linarith)
        simpa using hbn 
      simp [ih] at eq2 ⊢ 
      field_simp at eq2 ⊢
      ring_nf at eq2 ⊢ 
      <;> nlinarith [sq_nonneg (3 : ℝ), sq_nonneg (2 : ℝ)]
  
  have h2 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, b i = 1 / 4 * n ^ 2 - (1 / 3) ^ n + 1 := by 
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [eq1 (n)]
      rw [ih]
      field_simp at *
      ring_nf
  specialize h2 n
  simpa using h2