import Mathlib

theorem algebra_187185 {x y : ℝ} (h1 : (x - y) * x * y = 30) (h2 : (x + y) * x * y = 120) :
    x = 5 ∧ y = 3 := by
  have eq3 : x * y ^ 2 = 45 := by
    nlinarith
  have eq4 : x ^ 2 * y = 75 := by
    nlinarith
  have h3 : x ≠ 0 := by
    by_contra hx
    rw [hx] at h1 h2 eq3 eq4
    nlinarith
  have h4 : y ≠ 0 := by
    by_contra hy
    rw [hy] at h1 h2 eq3 eq4
    nlinarith
  have h9 : x = 5 / 3 * y := by
    apply (mul_left_inj' (show y ≠ 0 by exact h4)).mp 
    nlinarith [sq_pos_of_ne_zero h4, sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y)]
  have h8 : y ^ 3 = 27 := by
    rw [show x = 5 / 3 * y by linarith [h9]] at eq3
    nlinarith
  have h9 : y = 3 := by
    have h10 : y ^ 3 - 27 = 0 := by linarith
    have h11 : (y - 3) * (y ^ 2 + 3 * y + 9) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h11) with h12 h13
    · -- From $y - 3 = 0$
      linarith
    · -- From $y^2 + 3y + 9 = 0$
      have h14 : y ^ 2 + 3 * y + 9 ≠ 0 := by
        nlinarith [sq_nonneg (y + 3 / 2)]
      exfalso
      nlinarith [h14]
  have h10 : x = 5 := by
    nlinarith [h9, h4]
  exact ⟨h10, h9⟩