import Mathlib

theorem algebra_302763 {k : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ 8*x1^2 + 2*k*x1 + k - 1 = 0 ∧ 8*x2^2 + 2*k*x2 + k - 1 = 0 ∧ x1^2 + x2^2 = 1) :
    k = -2 := by 
  rcases h with ⟨x1, x2, h12, h1, h2, h3⟩
  have eq1 : 8 * (x1^2 - x2^2) + 2 * k * (x1 - x2) = 0 := by 
    nlinarith
  have eq2 : 8 * (x1 + x2) * (x1 - x2) + 2 * k * (x1 - x2) = 0 := by
    ring_nf at eq1 ⊢
    <;> linarith
  have ne : x1 - x2 ≠ 0 := by
    intro h'
    apply h12
    linarith
  have eq3 : 4 * (x1 + x2) + k = 0 := by 
    apply (mul_left_inj' ne).mp 
    linarith
  have eq4 : 8 * (x1^2 + x2^2) + 2 * k * (x1 + x2) + (k - 1) * 2 = 0 := by
    nlinarith [h1, h2]
  have eq5 : k = -4 * (x1 + x2) := by linarith [eq3]
  rw [eq5] at eq4
  have eq6 : k^2 - 4 * k - 12 = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by 
      intro h'
      apply h12
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2)]
  have eq7 : (k - 6) * (k + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq7) with eq8 eq8 
  · -- k = 6 doesn't work
    exfalso
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
      intro h'
      apply h12
      linarith 
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2)]
  · -- k = -2 works
    linarith