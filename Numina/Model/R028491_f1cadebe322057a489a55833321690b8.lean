import Mathlib

theorem algebra_248470 (a : ℝ) (h : ∃ x y, x ≠ y ∧ 2*x^2-(a+1)*x+(a-1)=0 ∧ 2*y^2-(a+1)*y+(a-1)=0 ∧ x-y=x*y) :
    a=2 := by
  rcases h with ⟨x, y, hneq, h1, h2, h3⟩
  have h4 : 2 * x ^ 2 - 2 * y ^ 2 - (a + 1) * (x - y) = 0 := by
    nlinarith
  have h5 : (x - y) * (2 * (x + y) - (a + 1)) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Case where x - y = 0, which leads to a contradiction
    exfalso
    apply hneq
    linarith
  · -- Case where 2(x + y) - (a + 1) = 0, which is our desired relation
    have h8 : 2 * (x + y) = a + 1 := by linarith
    have h9 : x * y = (a - 1) / 2 := by
      nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
        intro h'
        apply hneq
        linarith
      ), sq_nonneg (x - y), sq_nonneg (x + y), h1, h2, h8]
    have h10 : x - y = (a - 1) / 2 := by
      nlinarith [h3, h9]
    have h11 : x = a / 2 := by
      nlinarith [h8, h10]
    have h12 : y = 1 / 2 := by
      nlinarith [h11, h10]
    rw [h11] at h1
    nlinarith