import Mathlib

theorem algebra_119091 {a : ℕ → ℝ} (ha1 : a 1 = 0)
    (han : ∀ n ≥ 1, a (n + 1) = a n + Real.sqrt (4 * a n + 1) + 1) :
    ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, Real.sqrt (4 * a i + 1) = n ^ 2 := by

  have ha2 : ∀ n : ℕ, a (n + 1) = (↑n + 1 : ℝ) ^ 2 - (↑n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have h1 := han (n + 1) (by linarith)
      simp [show n + 1 ≥ 1 by linarith] at h1 ⊢
      rw [h1]
      rw [ih]
      have h2 : Real.sqrt (4 * ((↑n + 1 : ℝ) ^ 2 - (↑n + 1 : ℝ)) + 1) = (2 * (↑n + 1 : ℝ) - 1 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [sq_nonneg (2 * ((↑n + 1 : ℝ) ) - 1 : ℝ)]
      rw [h2]
      ring

  intro n hn
  have h3 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, Real.sqrt (4 * a i + 1) = (↑n : ℝ) ^ 2 := by 
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h4 : Real.sqrt (4 * a (n + 1) + 1) = (2 * (↑n : ℝ) + 1) := by 
        have ha3 : a (n + 1) = (↑n + 1 : ℝ) ^ 2 - (↑n + 1 : ℝ) := by 
          specialize ha2 n 
          simpa using ha2 
        have h5 : (4 * a (n + 1) + 1 : ℝ) = (2 * (↑n + 1 : ℝ) - 1) ^ 2 := by
          rw [ha3]
          nlinarith 
        have h6 : Real.sqrt (4 * a (n + 1) + 1 : ℝ) = Real.sqrt ((2 * (↑n + 1 : ℝ) - 1) ^ 2) := by 
          rw [h5] 
        rw [h6]
        have h7 : Real.sqrt ((2 * (↑n + 1 : ℝ) - 1 : ℝ) ^ 2) = (2 * (↑n + 1 : ℝ) - 1 : ℝ) := by
          rw [Real.sqrt_sq (by 
            nlinarith 
          )]
        rw [h7]
        <;> ring_nf 
      simp [h4]
      <;> ring_nf 
      <;> norm_num
  specialize h3 n 
  simpa using h3