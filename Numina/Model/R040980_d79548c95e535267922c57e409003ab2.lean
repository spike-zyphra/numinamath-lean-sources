import Mathlib

theorem algebra_227842 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + 2 * x * y + 3 * x * y * z = 115) :
    x + y + z = 10 ∨ x + y + z = 16 := by
  have h1 : x ∣ 115 := by
    use 1 + 2 * y + 3 * y * z
    ring_nf at h ⊢
    all_goals linarith
  have h2 : x = 1 ∨ x = 5 ∨ x = 23 ∨ x = 115 := by
    have h3 : x ≤ 115 := by
      exact Nat.le_of_dvd (by norm_num) h1
    interval_cases x <;> norm_num at h1 ⊢
    all_goals tauto
  rcases h2 with (h3 | h3 | h3 | h3)
  · -- x = 1
    rw [h3] at h
    have h4 : 1 + 2 * y + 3 * y * z = 115 := by
      nlinarith
    have h6 : y = 3 := by
      have h5 : y ∣ 114 := by
        use 2 + 3 * z
        nlinarith
      have h6 : y ≤ 114 := by
        exact Nat.le_of_dvd (by norm_num) h5
      interval_cases y <;> omega
    have h7 : z = 12 := by
      rw [h6] at h4
      nlinarith
    right
    omega
  · -- x = 5
    rw [h3] at h
    have h4 : 5 + 10 * y + 15 * y * z = 115 := by
      nlinarith
    have h6 : y = 2 := by
      have h5 : y ∣ 22 := by
        use 2 + 3 * z
        nlinarith
      have h6 : y ≤ 22 := by
        exact Nat.le_of_dvd (by norm_num) h5
      interval_cases y <;> omega
    have h7 : z = 3 := by
      rw [h6] at h4
      nlinarith
    left
    omega
  · -- x = 23
    rw [h3] at h
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  · -- x = 115
    rw [h3] at h
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]