import Mathlib

theorem algebra_14715 :
    IsGreatest {z | ∃ x y : ℤ, z = x + y ∧ x^2 + y^2 = 25} 7 := by
  constructor
  · -- Show that 7 belongs to the set
    use 3, 4
    all_goals norm_num
  · -- Show that for any z in the set, z ≤ 7
    intro z h
    rcases h with ⟨x, y, h_eq, h_eq_2⟩
    have h1 : x ≤ 5 := by nlinarith [sq_nonneg (x - 5 : ℤ), sq_nonneg (y), h_eq_2]
    have h2 : x ≥ -5 := by nlinarith [sq_nonneg (x + 5 : ℤ), sq_nonneg (y), h_eq_2]
    have h3 : y ≤ 5 := by nlinarith [sq_nonneg (y - 5 : ℤ), sq_nonneg (x), h_eq_2]
    have h4 : y ≥ -5 := by nlinarith [sq_nonneg (y + 5 : ℤ), sq_nonneg (x), h_eq_2]
    interval_cases x <;> interval_cases y
    <;> omega