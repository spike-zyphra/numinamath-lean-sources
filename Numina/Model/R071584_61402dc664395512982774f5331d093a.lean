import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_44293 {f : ℝ → ℝ} (hf : f = λ x => x ^ 3)
  (A B : ℝ) (hA : A ≠ B) (hB : f B = f A + deriv f A * (B - A)) :
  deriv f B = 4 * deriv f A := by
  have f_def : f = λ x => x ^ 3 := by exact hf
  have deriv_f : deriv f = fun x => 3 * x ^ 2 := by 
    rw [f_def]
    funext x
    simp [deriv_pow]
  have dA : deriv f A = 3 * A ^ 2 := by 
    rw [deriv_f]
  have dB : deriv f B = 3 * B ^ 2 := by 
    rw [deriv_f]
  have h1 : B ^ 3 = A ^ 3 + 3 * A ^ 2 * (B - A) := by 
    rw [f_def] at hB
    simp [dA] at hB ⊢
    linarith
  have h2 : B ^ 3 - 3 * A ^ 2 * B + 2 * A ^ 3 = 0 := by 
    nlinarith
  have h3 : (B - A) ^ 2 * (B + 2 * A) = 0 := by
    nlinarith [sq_nonneg (B - A), sq_nonneg (B - A), sq_nonneg (A), sq_nonneg (A - B), sq_nonneg (B + 2 * A)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case where $(B - A) ^ 2 = 0$
    have h4' : B - A = 0 := by 
      apply pow_eq_zero 
      exact h4
    have h4'' : B = A := by linarith
    exfalso
    exact hA (by linarith)
  · -- Case where $B + 2A = 0$
    have hB2 : B = -2 * A := by linarith
    rw [dB, hB2, dA]
    nlinarith [sq_pos_of_ne_zero (show A - B ≠ 0 by 
      intro h
      apply hA
      linarith
      )]

  all_goals nlinarith [sq_nonneg (B - A), sq_nonneg (B + 2 * A), sq_nonneg (A - B)]