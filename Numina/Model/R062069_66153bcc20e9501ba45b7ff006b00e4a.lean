import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_270535 (a : ℝ) (ha : 0 < a ∧ a < 1)
  (f : ℝ → ℝ → ℝ) (hf : f = λ x y => a * x + y) :
  IsGreatest {z | ∃ x y, z = f x y ∧ |x| + |y| ≤ 1} 1 := by
  constructor
  · -- Show that 1 is attained, hence it's in the set
    use 0, 1
    constructor
    · -- Show that f 0 1 = 1
      rw [hf]
      norm_num
    · -- Show that |0| + |1| ≤ 1
      norm_num
  · -- Show that any element in the set is ≤ 1
    intro z hz
    rcases hz with ⟨x, y, hfy, hineq⟩
    have h1 : a * x + y ≤ 1 := by
      cases' abs_cases x with hx hx
      · -- Case x ≥ 0
        cases' abs_cases y with hy hy
        · -- Case y ≥ 0
          nlinarith [ha.1, ha.2]
        · -- Case y ≤ 0
          nlinarith [ha.1, ha.2]
      · -- Case x ≤ 0
        cases' abs_cases y with hy hy
        · -- Case y ≥ 0
          nlinarith [ha.1, ha.2]
        · -- Case y ≤ 0
          nlinarith [ha.1, ha.2]
    -- Now we need to show that z ≤ 1
    have hz_eq : z = a * x + y := by
      rw [hfy, hf]
      all_goals simp
    linarith [hz_eq, h1]