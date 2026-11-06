import Mathlib

theorem algebra_195680 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 2 * Real.cos (40 * Real.pi / 180)) :
    x^4 + 1/x^4 = 2 * Real.cos (160 * Real.pi / 180) := by
  have eq1 : x ^ 2 + 1 / (x ^ 2) = (x + 1 / x) ^ 2 - 2 := by
    field_simp [hx]
    <;> ring
  have h1 : x ^ 2 + 1 / (x ^ 2) = (2 * Real.cos (40 * Real.pi / 180) ) ^ 2 - 2 := by 
    rw [eq1, h]
  
  have eq2 : x ^ 4 + 1 / (x ^ 4) = (x ^ 2 + 1 / (x ^ 2) ) ^ 2 - 2 := by 
    field_simp [hx]
    <;> ring
  
  rw [eq2, h1]

  have h2 : (2 * Real.cos (40 * Real.pi / 180) ) ^ 2 - 2 = 2 * Real.cos (80 * Real.pi / 180) := by
    have h3 : Real.cos (80 * Real.pi / 180) = 2 * Real.cos (40 * Real.pi / 180) ^ 2 - 1 := by
      have h4 : 80 * Real.pi / 180 = 2 * (40 * Real.pi / 180) := by ring_nf
      rw [h4]
      rw [Real.cos_two_mul]
      <;> ring
    rw [h3]
    ring_nf

  have h5 : (2 * Real.cos (80 * Real.pi / 180)) ^ 2 - 2 = 2 * Real.cos (160 * Real.pi / 180) := by 
    have h6 : Real.cos (160 * Real.pi / 180) = 2 * Real.cos (80 * Real.pi / 180) ^ 2 - 1 := by 
      have h7 : 160 * Real.pi / 180 = 2 * (80 * Real.pi / 180) := by ring_nf
      rw [h7]
      rw [Real.cos_two_mul]
      <;> ring
    rw [h6]
    ring_nf

  rw [h2, h5]