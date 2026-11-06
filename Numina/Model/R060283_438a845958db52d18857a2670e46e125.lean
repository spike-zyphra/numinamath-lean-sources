import Mathlib

theorem algebra_13846 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x < y) (hyz : y < z) (h : x + x * y + x * y * z = 37) :
    x + y + z ≤ 20 := by
  have h1 : x ∣ 37 := by
    use 1 + y + y * z 
    linarith
  have h2 : x = 1 ∨ x = 37 := by
    have h3 : x ≤ 37 := by
      exact Nat.le_of_dvd (by norm_num) h1
    interval_cases x <;> omega
  rcases h2 with h2 | h2
  · -- Case x = 1
    rw [h2] at h
    have h3 : y * (1 + z) = 36 := by
      nlinarith
    have y_div : y ∣ 36 := by
      use (1 + z)
      linarith
    have h4 : y ≤ 36 := by
      exact Nat.le_of_dvd (by norm_num) y_div
    interval_cases y <;> omega
  · -- Case x = 37
    rw [h2] at h
    nlinarith