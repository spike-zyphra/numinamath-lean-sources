import Mathlib

theorem number_theory_63869 :
  IsGreatest {w : ℕ | ∃ x y z, x.Prime ∧ y.Prime ∧ z.Prime ∧ x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x + y + z = 49 ∧ w = x * y * z} 4199 := by
  constructor
  · -- Show that 4199 is in the set
    use 17, 13, 19
    all_goals norm_num
  · -- Show that 4199 is the greatest element in the set
    intro w hw
    rcases hw with ⟨x, y, z, hx, hy, hz, hxy, hyz, hzx, hsum, heq⟩
    have h1 : x ≤ 49 := by
      omega
    have h2 : y ≤ 49 := by
      omega
    have h3 : z ≤ 49 := by
      omega
    interval_cases x <;> interval_cases y
    <;> norm_num at hx hy hxy hyz hsum heq
    <;> omega