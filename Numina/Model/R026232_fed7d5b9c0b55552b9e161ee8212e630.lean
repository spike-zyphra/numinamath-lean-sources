import Mathlib

theorem algebra_281847 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : ∃ r, 3 * x * r = 4 * y ∧ 4 * y * r = 5 * z)
    (h2 : ∃ d, 1 / x + d = 1 / y ∧ 1 / y + d = 1 / z) :
    x / z + z / x = 34 / 15 := by
  rcases h1 with ⟨r, h11, h12⟩
  rcases h2 with ⟨d, h21, h22⟩
  have eq3 : 16 * y ^ 2 = 15 * (x * z) := by
    have eq1 : 3 * x * r = 4 * y := h11
    have eq2 : 4 * y * r = 5 * z := h12 
    have eq3 : r = 4 * y / (3 * x) := by
      field_simp [hx, hy]
      linarith
    rw [eq3] at eq2
    field_simp [hx, hy] at eq2
    nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
  have eq5 : 2 * (x * z) = y * (x + z) := by
    have eq1 : 1 / x + d = 1 / y := h21
    have eq2 : 1 / y + d = 1 / z := h22
    have h3 : d = 1 / y - 1 / x := by linarith [eq1]
    rw [h3] at eq2
    field_simp [hx, hy, hz] at eq1 eq2
    nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero hz]
  have h3 : x / z + z / x = (x^2 + z^2) / (x * z) := by
    field_simp [hx, hz]
    <;> ring
  rw [h3]
  have h4 : x^2 + z^2 = (x + z) ^ 2 - 2 * (x * z) := by
    nlinarith
  rw [h4]
  have h5 : (x + z) ^ 2 = (4 * (x * z) ^ 2) / (y ^ 2) := by
    have eq6 : y * (x + z) = 2 * (x * z) := by
      linarith [eq5]
    have hy1 : y ≠ 0 := hy
    have h6 : (x + z) = (2 * (x * z) ) / y := by
      field_simp [hy1] at eq6 ⊢
      <;> nlinarith 
    calc
      (x + z) ^ 2 = ((2 * (x * z) ) / y) ^ 2 := by 
        rw [h6]
      _ = (4 * (x * z) ^ 2) / (y ^ 2) := by 
        field_simp [hy1]
        <;> ring
  have h6 : ( (x + z) ^ 2 - 2 * (x * z) ) / (x * z) = (4 * (x * z) / (y^2)) - 2 := by
    have eq7 : (x + z) ^ 2 = (4 * (x * z) ^ 2) / (y ^ 2) := h5
    have h8 : (x * z) ≠ 0 := by
      apply mul_ne_zero
      exact hx
      exact hz
    have h9 : y ≠ 0 := hy
    field_simp [h8, h9] at eq7 ⊢
    nlinarith [eq7, sq_pos_of_ne_zero h8, sq_pos_of_ne_zero h9, sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hz]
  rw [h6]
  have h9 : (4 * (x * z) / (y ^ 2)) = 64 / 15 := by
    have eq8 : 16 * y^2 = 15 * (x * z) := eq3
    have hy1 : y ≠ 0 := hy
    have h7 : (x * z) ≠ 0 := by
      apply mul_ne_zero
      exact hx
      exact hz
    have hy2 : y^2 ≠ 0 := by
      apply pow_ne_zero
      exact hy
    field_simp [h7, hy2] at eq8 ⊢
    <;> nlinarith [eq8, sq_pos_of_ne_zero h7, sq_pos_of_ne_zero hy2, sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hz]
  rw [h9]
  all_goals norm_num