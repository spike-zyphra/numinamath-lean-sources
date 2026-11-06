import Mathlib

theorem number_theory_170555 :
    IsLeast {n | ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x^2 + y^2 = z^3 ∧ n = x + y + z} 18 := by
  constructor
  · -- First part: show 18 is in the set.
    use 2, 11, 5
    all_goals norm_num
  · -- Second part: show that 18 is the smallest.
    intro n hn
    rcases hn with ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, heq, hn⟩
    by_contra h
    push_neg at h
    have h1 : x + y + z < 18 := by
      omega
    have h2 : x ≤ 15 := by
      omega
    have h3 : y ≤ 15 := by
      omega
    have h4 : z ≤ 16 := by
      omega
    interval_cases x <;> interval_cases y <;> interval_cases z
    <;> omega