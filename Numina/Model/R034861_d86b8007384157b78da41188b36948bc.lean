import Mathlib

theorem algebra_21850 {x : ℝ} (hx : x ≠ 0) (h : 3 * x + 1 / (2 * x) = 3) :
    64 * x ^ 6 + 1 / (729 * x ^ 6) = 416 / 27 := by
  have h1 : 2 * x + 1 / (3 * x) = 2 := by 
    have h2 : 3 * x + 1 / (2 * x) = 3 := h 
    have h3 : 2 * x + 1 / (3 * x) = (2 / 3) * (3 * x + 1 / (2 * x)) := by 
      field_simp [hx] 
      <;> ring 
    rw [h3, h2]
    norm_num 
  have h2 : 4 * x ^ 2 + 1 / (9 * x ^ 2) = 8 / 3 := by
    have h3 : 4 * x ^ 2 + 1 / (9 * x ^ 2) = (2 * x + 1 / (3 * x)) ^ 2 - 4 / 3 := by
      field_simp [hx]
      <;> ring
    rw [h3, h1]
    norm_num
  have h3 : 64 * x ^ 6 + 1 / (729 * x ^ 6) = (4 * x ^ 2) ^ 3 + (1 / (9 * x ^ 2)) ^ 3 := by
    field_simp [hx]
    <;> ring
  have h4 : (4 * x ^ 2 : ℝ) ^ 3 + (1 / (9 * x ^ 2)) ^ 3 = 
    (4 * x ^ 2 + 1 / (9 * x ^ 2)) ^ 3 - 3 * (4 * x ^ 2 + 1 / (9 * x ^ 2)) * (4 * x ^ 2 * (1 / (9 * x ^ 2)) ) := by
    ring 
  have h9 : (4 * x ^ 2 : ℝ) * (1 / (9 * x ^ 2)) = 4 / 9 := by 
    field_simp [hx] 
    <;> ring_nf 
  rw [h3, h4, h2, h9]
  norm_num