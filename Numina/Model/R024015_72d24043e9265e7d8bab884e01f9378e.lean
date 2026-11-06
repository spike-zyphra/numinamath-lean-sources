import Mathlib

theorem algebra_174057 {x y z : ℕ} (h1 : y = (x / 2) + 2) (h2 : z = (y / 2) + 2)
    (h3 : x * y * z = 1120) :
    x = 16 ∧ y = 10 ∧ z = 7 := by
  have hx1 : x ≤ 19 := by
    by_contra h
    push_neg at h
    have h5 : y ≥ 12 := by
      have : x ≥ 20 := by omega
      omega
    have h6 : z ≥ 8 := by
      have h7 : y ≥ 12 := by omega
      omega
    have h8 : x * y * z > 1120 := by
      have hx20 : x ≥ 20 := by omega
      have h5 : y ≥ 12 := by omega
      have h6 : z ≥ 8 := by omega
      have : x * y * z ≥ 20 * 12 * 8 := by
        have h9 : x ≥ 20 := by omega
        have h10 : y ≥ 12 := by omega
        have h11 : z ≥ 8 := by omega
        have h12 : x * y ≥ 20 * 12 := by
          nlinarith
        nlinarith
      omega
    linarith
  have hy : y ≤ 11 := by
    have hx19 : x ≤ 19 := by linarith
    omega
  have hz7 : z ≤ 7 := by
    have hy11 : y ≤ 11 := by linarith
    omega
  interval_cases x <;> norm_num [h1] at h2 h3
  <;> omega