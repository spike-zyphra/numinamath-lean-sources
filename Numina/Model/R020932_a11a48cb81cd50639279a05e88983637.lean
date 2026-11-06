import Mathlib

theorem algebra_63952 {b c : ℝ} (P : ℝ → ℝ) (hP : ∀ x, P x = x ^ 2 + b * x + c)
    (hP1 : P (P 1) = 0) (hP2 : P (P (-2)) = 0) (hP3 : P 1 ≠ P (-2)) : P 0 = -5 / 2 := by
  have eq1 : P 1 = 1 + b + c := by
    rw [hP]
    <;> ring
  have eq2 : P (-2) = 4 - 2 * b + c := by
    rw [hP]
    <;> ring
  have eq3 : P (P 1) = (P 1) ^ 2 + b * (P 1) + c := by
    apply hP
  have eq4 : P (P (-2)) = (P (-2)) ^ 2 + b * (P (-2)) + c := by
    apply hP
  rw [eq3] at hP1
  rw [eq4] at hP2
  rw [eq1] at hP1
  rw [eq2] at hP2
  have h1 : (1 + b + c) ^ 2 + b * (1 + b + c) + c = 0 := by 
    linarith
  have h2 : (4 - 2 * b + c) ^ 2 + b * (4 - 2 * b + c) + c = 0 := by 
    linarith
  have h3 : (1 + b + c) ^ 2 - (4 - 2 * b + c) ^ 2 + b * ((1 + b + c) - (4 - 2 * b + c)) = 0 := by 
    linarith
  have h4 : (5 + 2 * c) * (-3 + 3 * b) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- $5 + 2c = 0$, so $c = -5/2$
    have hc : c = -5 / 2 := by linarith
    have hP0 : P 0 = c := by
      rw [hP]
      all_goals norm_num
    rw [hP0]
    linarith
  · -- $-3 + 3b = 0$, so $b = 1$
    have hb : b = 1 := by linarith
    have hP1' : P 1 = P (-2) := by
      rw [eq1, eq2]
      linarith [hb]
    contradiction