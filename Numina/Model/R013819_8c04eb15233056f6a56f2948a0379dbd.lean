import Mathlib

theorem algebra_70324 :
    IsGreatest {m | ∃ x y z : ℕ, x + y + z = 1000 ∧ m = 11 * x * y + 3 * x + 2012 * y * z} 503000000 := by
  constructor
  · -- Show 503000000 is in the set.
    use 0, 500, 500
    all_goals norm_num
  · -- Show 503000000 is greatest in the set.
    intro m hm
    rcases hm with ⟨x, y, z, h1, hm⟩
    have h2 : z = 1000 - x - y := by
      omega
    rw [h2] at hm
    have h3 : x ≤ 1000 := by
      omega
    have h4 : y ≤ 1000 := by
      omega
    interval_cases y <;> omega