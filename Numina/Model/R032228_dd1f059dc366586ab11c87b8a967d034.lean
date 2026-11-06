import Mathlib

theorem algebra_21334 : IsLeast {x + y | (x : ℕ) (y : ℕ) (_ : x > 0) (_ : y > 0) (_ : x ≥ (2 * y / 3 : ℚ) + 3) (_ : x ≤ 2 * y)} 8 := by
  constructor
  · -- Show that 8 is in the set.
    use 5, 3
    norm_num
  · -- Show that any total in the set is at least 8.
    intro z h
    rcases h with ⟨x, y, hx_pos, hy_pos, h1, h2, hz⟩
    by_contra h
    push_neg at h
    have h3 : x + y < 8 := by linarith
    have h4 : x ≤ 7 := by
      omega
    have h5 : y ≤ 7 := by
      omega
    interval_cases x <;> interval_cases y
    <;> norm_num at h1 h2 hz
    <;> omega