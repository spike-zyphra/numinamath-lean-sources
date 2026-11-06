import Mathlib

theorem algebra_3859 : IsGreatest {n : ℤ | ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x < 5 ∧ y < 5 ∧ z < 5 ∧ n = (x ^ y) ^ z} (3 ^ 8) := by
  constructor
  · -- Show that 3^8 is in the set
    use 3, 4, 2
    all_goals norm_num
  · -- Show that any n in the set is ≤ 3^8
    intro n hn
    rcases hn with ⟨x, y, z, hx1, hy1, hz1, hxy, hyz, hzx, hx2, hy2, hz2, hn⟩
    have h1 : x < 5 := by linarith
    have h2 : y < 5 := by linarith
    have h3 : z < 5 := by linarith
    interval_cases x <;> interval_cases y <;> interval_cases z
    <;> norm_num at hn hxy hyz hzx
    <;> norm_num [hn]
    <;> omega