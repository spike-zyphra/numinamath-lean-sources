import Mathlib

theorem algebra_234770 {x y z a b c : ℝ} (h1 : x ≠ 0) (h2 : y ≠ 0) (h3 : z ≠ 0)
    (h4 : a ≠ 0) (h5 : b ≠ 0) (h6 : c ≠ 0) (h7 : x / a + y / b + z / c = 1) (h8 : a / x + b / y + c / z = 0) :
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 1 := by
  have h9 : x / a + y / b + z / c = 1 := h7
  have eq1 : x^2 / a^2 + y^2 / b^2 + z^2 / c^2 =
    (x / a + y / b + z / c) ^ 2 - 2 * ( (x * y / (a * b) ) + (x * z / (a * c)) + (y * z / (b * c)) ) := by
    field_simp [h1, h2, h3, h4, h5, h6]
    ring
    <;> field_simp [h1, h2, h3, h4, h5, h6]
    <;> ring
  have h10 : (x * y / (a * b) ) + (x * z / (a * c)) + (y * z / (b * c) ) = 0 := by
    have h_eq : a / x + b / y + c / z = 0 := h8
    have eq2 : a * y * z + b * x * z + c * x * y = 0 := by
      field_simp [h1, h2, h3] at h_eq
      linarith
    have eq3 : (x * y / (a * b) ) + (x * z / (a * c)) + (y * z / (b * c) ) = (a * y * z + b * x * z + c * x * y) / (a * b * c) := by
      field_simp [h1, h2, h3, h4, h5, h6]
      ring_nf
      <;> field_simp [h1, h2, h3, h4, h5, h6]
      <;> ring
    rw [eq3, eq2]
    norm_num [h4, h5, h6]
    <;> ring_nf
    <;> field_simp [h1, h2, h3, h4, h5, h6]
    <;> ring
  rw [eq1, h9, h10]
  all_goals norm_num
  <;> nlinarith
  <;> nlinarith [h4, h5, h6]
  <;> try { norm_num }
  all_goals try { try { norm_num } <;> tauto }
  all_goals linarith [h7, h8]