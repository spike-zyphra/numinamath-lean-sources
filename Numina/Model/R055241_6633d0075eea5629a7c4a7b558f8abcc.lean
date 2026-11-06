import Mathlib

theorem algebra_10276 :
    IsGreatest {x | ∃ a b, x = a + b ∧ a^2 + b^2 = 90 ∧ a * b = 27} 12 := by
  constructor
  · -- Show that 12 is obtained by some a and b
    use 9, 3
    all_goals norm_num
  · -- Show that any element in the set is at most 12
    intro x hx
    rcases hx with ⟨a, b, h1, h2, h3⟩
    have h4 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by ring
    rw [h2, h3] at h4
    have h5 : (a + b) ^ 2 = 144 := by linarith
    have h6 : a + b ≤ 12 := by
      nlinarith [sq_nonneg (a + b - 12), sq_nonneg (a + b + 12)]
    linarith