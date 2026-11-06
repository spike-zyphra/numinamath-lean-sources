import Mathlib

theorem algebra_11866 {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ n → a n > 0)
    (h1 : a 1 = 1) (h2 : ∀ n, 4 * a (n + 1) = 5 * a n + Real.sqrt (9 * (a n)^2 + 16)) :
    ∀ n, 1 ≤ n → a n = (2 / 3) * (2^n - 1 / 2^n) := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      rw [h1]
      norm_num
    | succ n => 
      -- induction step
      have ih1 := ih (by linarith)
      have h3 := h2 (n + 1)
      have h4 : 4 * a ((n + 1) + 1) = 5 * a (n + 1) + Real.sqrt (9 * (a (n + 1)) ^ 2 + 16) := by
        simpa using h2 (n + 1)
      rw [ih1] at h4
      have h5 : Real.sqrt (9 * ((2 / 3) * (2 ^ (n + 1) - 1 / 2 ^ (n + 1))) ^ 2 + 16) = 2 ^ (n + 2) + 2 / (2 ^ (n + 1)) := by
        have h_eq : (9 * ((2 / 3) * (2 ^ (n + 1) - 1 / 2 ^ (n + 1))) ^ 2 + 16 : ℝ) = 
          (2 ^ (n + 2) + 2 / (2 ^ (n + 1)) : ℝ) ^ 2 := by
          field_simp at *
          ring_nf
          <;> norm_num
          <;> ring_nf
          <;> norm_num
          all_goals nlinarith
        rw [h_eq]
        rw [Real.sqrt_sq (by positivity)]
      rw [h5] at h4
      have eq1 : a ((n + 1) + 1) = (2 / 3) * (2 ^ (n + 2) - 1 / (2 ^ (n + 2))) := by
        have eq2 : 4 * a ((n + 1) + 1) = 5 * ((2 / 3) * (2 ^ (n + 1) - 1 / (2 ^ (n + 1)) )) + (2 ^ (n + 2) + 2 / (2 ^ (n + 1))) := by
          linarith [h4]
        have eq3 : a ((n + 1) + 1) = ((5 * ((2 / 3) * (2 ^ (n + 1) - 1 / (2 ^ (n + 1)) )) + (2 ^ (n + 2) + 2 / (2 ^ (n + 1))) ) / 4) := by
          linarith
        rw [eq3]
        field_simp at *
        ring_nf
        <;> field_simp
        <;> ring
        all_goals try { 
          ring_nf at *
          field_simp
          nlinarith [Real.sqrt_nonneg (9 * ((2 / 3) * (2 ^ (n + 1) - 1 / (2 ^ (n + 1))) ^ 2 + 16))]
        }
        <;> nlinarith
      exact_mod_cast eq1