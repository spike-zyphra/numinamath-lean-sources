import Mathlib

theorem algebra_313118 (P : ℝ → ℝ → ℝ)
    (hP : P = fun a b => 2 * a ^ 2 - 8 * a * b + 17 * b ^ 2 - 16 * a - 4 * b + 2070) :
    IsLeast {x | ∃ a b, x = P a b} 2002 := by
  constructor
  · -- Show that 2002 is in the set
    use 8, 2
    simp [hP]
    all_goals norm_num
  · -- Show that 2002 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, hx⟩
    simp [hP] at hx
    nlinarith [sq_nonneg (a - 2 * b - 4), sq_nonneg (b - 2)]