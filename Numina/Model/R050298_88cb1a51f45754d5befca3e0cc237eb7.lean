import Mathlib

theorem algebra_318929 {z : ℂ} (hz : z^3 = 27) : z^5 + 3 * z^4 + 2242 = 2728 ∨ z^5 + 3 * z^4 + 2242 = 1999 := by 
  have h1 : z^3 - 27 = 0 := by
    rw [hz]
    ring_nf
  have h2 : z^3 - 27 = (z - 3) * (z^2 + 3 * z + 9) := by
    ring_nf
  rw [h2] at h1
  cases (mul_eq_zero.mp h1) with
  | inl h3 =>
    have hz3 : z = 3 := by
      exact eq_of_sub_eq_zero h3
    rw [hz3]
    norm_num
    all_goals norm_num
  | inr h4 =>
    have hz2 : z^2 = -3 * z - 9 := by
      calc
        z^2 = z^2 + 3 * z + 9 - 3 * z - 9 := by ring_nf
        _ = 0 - 3 * z - 9 := by rw [h4]
        _ = -3 * z - 9 := by ring_nf
    have hz4 : z^4 = 27 * z := by
      calc
        z^4 = z * z^3 := by ring_nf
        _ = z * 27 := by rw [hz]
        _ = 27 * z := by ring_nf
    have hz5 : z^5 = -81 * z - 243 := by
      calc
        z^5 = z^2 * z^3 := by ring_nf
        _ = z^2 * 27 := by rw [hz]
        _ = 27 * z^2 := by ring_nf
        _ = 27 * (-3 * z - 9) := by rw [hz2]
        _ = -81 * z - 243 := by ring_nf
    rw [hz5, hz4]
    norm_num
    <;> ring_nf <;> norm_num