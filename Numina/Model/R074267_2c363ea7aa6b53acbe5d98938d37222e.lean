import Mathlib

theorem algebra_35084 {a : ℝ} (ha : a ≠ -1) (h : a^5 + 5 * a^4 + 10 * a^3 + 3 * a^2 - 9 * a - 6 = 0) :
    (a + 1)^3 = 7 := by
  have h1 : (a + 1)^2 * (a^3 + 3 * a^2 + 3 * a - 6) = 0 := by
    ring_nf at h ⊢
    linarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where (a + 1)^2 = 0
    have h4 : a + 1 = 0 := by
      apply pow_eq_zero 
      exact h2
    have h5 : a = -1 := by linarith
    exfalso
    exact ha h5
  · -- Case where a^3 +3a^2 +3a -6 =0 
    nlinarith [sq_pos_of_ne_zero (show a + 1 ≠ 0 by intro h'; apply ha; linarith)]