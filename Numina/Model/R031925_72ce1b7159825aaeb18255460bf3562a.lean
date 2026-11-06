import Mathlib

theorem algebra_22656 :
    IsGreatest {e | ∃(a b c d : ℝ), a + b + c + d + e = 8 ∧  
                    a^2 + b^2 + c^2 + d^2 + e^2 = 16} (16 / 5) := by
  constructor
  · -- Show that 16/5 is in the set, i.e., is achievable
    use 6 / 5, 6 / 5, 6 / 5, 6 / 5
    constructor
    · norm_num
    · norm_num
  · -- Show that 16/5 is the greatest element in the set
    intro e he
    rcases he with ⟨a, b, c, d, he1, he2⟩
    have h1 : (a + b + c + d) ^ 2 ≤ 4 * (a^2 + b^2 + c^2 + d^2) := by
      linarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
    have h2 : (a + b + c + d) = 8 - e := by linarith
    have h3 : a^2 + b^2 + c^2 + d^2 = 16 - e^2 := by linarith
    rw [h2, h3] at h1
    nlinarith [sq_nonneg (e * 5 - 16), sq_nonneg (e - 16 / 5)]