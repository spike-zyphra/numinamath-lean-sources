import Mathlib

theorem algebra_13058 :
    IsGreatest {x : ℝ | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 10 ∧ x = a * b * c + 3 * a * b - 2 * a * c + b * c - 6 * a + 3 * b - 2 * c} 70 := by
  constructor
  · -- Show 70 is in the set.
    use 3, 6, 1
    norm_num
  · -- Show that 70 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq10, hx_eq⟩
    have h1 : c = 10 - a - b := by linarith
    rw [h1] at hx_eq
    have hc10 : 0 ≤ 10 - a - b := by
      nlinarith
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 6), sq_nonneg ( (10 - a - b) - 1 ), 
      sq_nonneg (a - 3 + b - 6), sq_nonneg (a - 3 - (b - 6)), 
      mul_nonneg ha hb, mul_nonneg hb hc10, mul_nonneg hc10 ha ]