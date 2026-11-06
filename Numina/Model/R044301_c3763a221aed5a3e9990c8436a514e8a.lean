import Mathlib

theorem algebra_250696 {x y z : ℝ} (h : x ≠ y ∧ y ≠ z ∧ z ≠ x) :
    ((x ^ 2 - y ^ 2) ^ 3 + (y ^ 2 - z ^ 2) ^ 3 + (z ^ 2 - x ^ 2) ^ 3) /
    ((x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3) = (x + y) * (y + z) * (z + x) := by 
  rcases h with ⟨hx1, hy1, hz1⟩
  have hx2 : x - y ≠ 0 := by
    intro h'
    apply hx1
    linarith
  have hy2 : y - z ≠ 0 := by
    intro h'
    apply hy1
    linarith
  have hz2 : z - x ≠ 0 := by
    intro h'
    apply hz1
    linarith
  have h1 : ((x ^ 2 - y ^ 2) ^ 3 + (y ^ 2 - z ^ 2) ^ 3 + (z ^ 2 - x ^ 2) ^ 3) =
      3 * ((x ^ 2 - y ^ 2) * (y ^ 2 - z ^ 2) * (z ^ 2 - x ^ 2)) := by
    have h2 : (x ^ 2 - y ^ 2) + (y ^ 2 - z ^ 2) + (z ^ 2 - x ^ 2) = (0 : ℝ) := by
      ring
    have h3 : (x ^ 2 - y ^ 2) ^ 3 + (y ^ 2 - z ^ 2) ^ 3 + (z ^ 2 - x ^ 2) ^ 3 =
        3 * ((x ^ 2 - y ^ 2) * (y ^ 2 - z ^ 2) * (z ^ 2 - x ^ 2)) := by 
      have h4 : (x ^ 2 - y ^ 2) ^ 3 + (y ^ 2 - z ^ 2) ^ 3 + (z ^ 2 - x ^ 2) ^ 3 - 3 * ((x ^ 2 - y ^ 2) * (y ^ 2 - z ^ 2) * (z ^ 2 - x ^ 2)) = 
          ((x ^ 2 - y ^ 2) + (y ^ 2 - z ^ 2) + (z ^ 2 - x ^ 2)) * ((x ^ 2 - y ^ 2) ^ 2 + (y ^ 2 - z ^ 2) ^ 2 + (z ^ 2 - x ^ 2) ^ 2 - ((x ^ 2 - y ^ 2) * (y ^ 2 - z ^ 2)) - ((x ^ 2 - y ^ 2) * (z ^ 2 - x ^ 2)) - ((y ^ 2 - z ^ 2) * (z ^ 2 - x ^ 2))) := by ring
      rw [h2] at h4
      have h5 : (x ^ 2 - y ^ 2) ^ 3 + (y ^ 2 - z ^ 2) ^ 3 + (z ^ 2 - x ^ 2) ^ 3 - 3 * ((x ^ 2 - y ^ 2) * (y ^ 2 - z ^ 2) * (z ^ 2 - x ^ 2)) = (0 : ℝ) := by
        rw [h4]
        norm_num
      linarith
    linarith
  have h2 : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 = 3 * ((x - y) * (y - z) * (z - x)) := by
    have h3 : (x - y) + (y - z) + (z - x) = (0 : ℝ) := by
      ring
    have h4 : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 = 3 * ((x - y) * (y - z) * (z - x)) := by 
      have h5 : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 - 3 * ((x - y) * (y - z) * (z - x)) = ((x - y) + (y - z) + (z - x)) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 - ((x - y) * (y - z)) - ((x - y) * (z - x)) - ((y - z) * (z - x))) := by ring
      rw [h3] at h5
      have h6 : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 - 3 * ((x - y) * (y - z) * (z - x)) = (0 : ℝ) := by
        rw [h5]
        norm_num
      linarith
    linarith
  rw [h1, h2]
  field_simp [show (x - y) * (y - z) * (z - x) ≠ 0 by
    apply mul_ne_zero
    apply mul_ne_zero
    exact hx2
    exact hy2
    exact hz2
  ]
  <;> ring