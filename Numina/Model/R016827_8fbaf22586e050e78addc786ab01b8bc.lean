import Mathlib

theorem algebra_155574 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : ∃ r, 4 * y = 3 * x * r ∧ 5 * z = 4 * y * r)
    (h2 : ∃ d, 1 / y = 1 / x + d ∧ 1 / z = 1 / y + d) :
    x / z + z / x = 34 / 15 := by 
  rcases h1 with ⟨r, h11, h12⟩
  rcases h2 with ⟨d, h21, h22⟩
  have eq6 : 16 * y ^ 2 = 15 * x * z := by 
    have h3 : 4 * y = 3 * x * r := h11
    have h4 : 5 * z = 4 * y * r := h12
    have eq3 : r = 4 * y / (3 * x) := by 
      have h3 : 3 * x ≠ 0 := by
        intro h4
        have h5 : x = 0 := by
          linarith
        contradiction
      field_simp at *
      nlinarith
    have eq4 : r = 5 * z / (4 * y) := by 
      have h4 : 4 * y ≠ 0 := by
        intro h
        apply hy
        linarith
      field_simp at *
      nlinarith
    have eq5 : 4 * y / (3 * x) = 5 * z / (4 * y) := by 
      linarith [eq3, eq4]
    have h3 : 3 * x ≠ 0 := by
      intro h
      have h4 : x = 0 := by
        linarith
      contradiction
    have h4 : 4 * y ≠ 0 := by
      intro h
      apply hy
      linarith
    field_simp [h3, h4] at eq5 ⊢
    nlinarith 
  have eq7 : x * y + y * z = 2 * x * z := by 
    have eq3 : 1 / y = 1 / x + d := h21
    have eq4 : 1 / z = 1 / y + d := h22
    have eq8 : d = 1 / y - 1 / x := by linarith
    rw [eq8] at eq4
    field_simp [hx, hy, hz] at eq3 eq4 ⊢
    nlinarith 
  have eq8 : x * z = 16 * y^2 / 15 := by
    linarith [eq6]
  have eq9 : x + z = 32 * y / 15 := by
    have h4 : y * (x + z) = 2 * (x * z) := by
      linarith [eq7]
    rw [show x * z = 16 * y ^ 2 / 15 by linarith [eq8]] at h4
    have h5 : y ≠ 0 := hy
    have h6 : x + z = 32 * y / 15 := by
      apply (mul_left_inj' h5).mp
      linarith
      all_goals linarith
    linarith
  have eq10 : x ^ 2 + z ^ 2 = 544 * y^2 / 225 := by
    have hx2 : x ^ 2 + z ^ 2 = (x + z) ^ 2 - 2 * (x * z) := by
      ring 
    rw [hx2, eq9, eq8]
    nlinarith 
  have eq11 : x / z + z / x = (x ^ 2 + z ^ 2) / (x * z) := by 
    field_simp [hx, hz]
    <;> ring 
  rw [eq11]
  rw [show x * z = 16 * y ^ 2 / 15 by linarith [eq8], eq10]
  have hy2 : y^2 ≠ 0 := by
    apply pow_ne_zero 2
    exact hy
  field_simp [hy2]
  <;> nlinarith
  <;> nlinarith