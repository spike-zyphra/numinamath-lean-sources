import Mathlib

theorem algebra_155554 (a : ℝ) (ha : a ≠ 0) (h : (Nat.choose 5 4) * a^4 = (Nat.choose 5 3) * a^3) :
    a = 2 := by 
  have h1 : (Nat.choose 5 4 : ℝ) = 5 := by norm_num [Nat.choose]
  have h2 : (Nat.choose 5 3 : ℝ) = 10 := by norm_num [Nat.choose]
  rw [h1] at h
  rw [h2] at h
  have eq1 : 5 * a^4 = 10 * a^3 := by 
    linarith
  have eq2 : 5 * a^3 * (a - 2) = 0 := by 
    nlinarith [sq_nonneg (a) ]
  cases' (mul_eq_zero.mp eq2) with h3 h4
  · -- Case where `5 * a^3 = 0`
    have h5 : a^3 = 0 := by
      nlinarith
    have h6 : a = 0 := by
      have h7 : a^3 = 0 := by
        linarith
      have h8 : a = 0 := by
        have h9 : a^3 = 0 := by
          linarith
        have h10 : a = 0 := by 
          have h11 : a^3 = 0 := by
            linarith
          simp at h11 ⊢
          <;> tauto
        linarith
      linarith
    contradiction 
  · -- Case where `a - 2 = 0`
    linarith