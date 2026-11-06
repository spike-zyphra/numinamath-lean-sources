import Mathlib

theorem algebra_12106 (k : ℤ) (h : ∃ a d, (36 + k) = a^2 ∧ (300 + k) = (a + d)^2 ∧ (596 + k) = (a + 2 * d)^2) :
    k = 925 := by
  rcases h with ⟨a, d, h1, h2, h3⟩
  have eq1 : 264 = d * (2 * a + d) := by
    nlinarith
  have eq2 : 296 = d * (2 * a + 3 * d) := by
    nlinarith
  have eq3 : d ^ 2 = 16 := by
    have h4 : 296 - 264 = 32 := by norm_num
    nlinarith [sq_nonneg (d), sq_nonneg (a), sq_nonneg (d - 4), sq_nonneg (d + 4), sq_nonneg (a - 31), sq_nonneg (a + 31)]
  have eq4 : d = 4 ∨ d = -4 := by
    have h4 : d ^ 2 - 16 = 0 := by linarith
    have h5 : (d - 4) * (d + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · left
      linarith
    · right
      linarith
  cases eq4 with
  | inl h4 =>
    have eq5 : a = 31 := by
      rw [h4] at eq1
      nlinarith
    nlinarith
  | inr h4 =>
    have eq5 : a = -31 := by
      rw [h4] at eq1
      nlinarith
    nlinarith