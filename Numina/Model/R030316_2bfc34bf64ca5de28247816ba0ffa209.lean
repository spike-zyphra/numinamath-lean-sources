import Mathlib

theorem algebra_176715 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x + 2 * y = z) (h2 : x ^ 2 - 4 * y ^ 2 + z ^ 2 = 310) :
    x * y * z = 11935 ∨ x * y * z = 2015 := by
  have h4 : z = x + 2 * y := by linarith
  rw [h4] at h2
  have h5 : x * (x + 2 * y) = 155 := by
    nlinarith
  have h7 : x ∣ 155 := by
    use x + 2 * y
    linarith [h5]
  have h8 : x = 1 ∨ x = 5 ∨ x = 31 ∨ x = 155 := by 
    have h9 : x ∣ 155 := h7
    have h10 : x ≤ 155 := by
      exact Int.le_of_dvd (by norm_num) h9
    interval_cases x <;> tauto
  rcases h8 with (h | h | h | h)
  · -- x = 1
    have hx1 : x = 1 := h
    have hy1 : y = 77 := by
      rw [hx1] at h5
      nlinarith
    have hz1 : z = 155 := by 
      linarith [h1, hx1, hy1]
    left
    rw [hx1, hy1, hz1]
    all_goals norm_num
  · -- x = 5
    have hx5 : x = 5 := h
    have hy5 : y = 13 := by
      rw [hx5] at h5
      nlinarith
    have hz5 : z = 31 := by 
      linarith [h1, hx5, hy5]
    right
    rw [hx5, hy5, hz5]
    all_goals norm_num
  · -- x = 31
    have hx31 : x = 31 := h
    -- This will lead to a contradiction as y is negative
    have h9 : y = -13 := by
      rw [hx31] at h5
      nlinarith
    linarith [show y > 0 from hy, show y < 0 from by linarith [h9]]
  · -- x = 155
    have hx155 : x = 155 := h
    -- This will lead to a contradiction as y is negative
    have h10 : y = -77 := by
      rw [hx155] at h5
      nlinarith
    linarith [show y > 0 from hy, show y < 0 from by linarith [h10]]