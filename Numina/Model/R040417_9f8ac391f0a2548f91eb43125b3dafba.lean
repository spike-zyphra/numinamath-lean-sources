import Mathlib


theorem algebra_286422 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : ∃ r, 4 * y = 3 * x * r ∧ 5 * z = 4 * y * r)
    (h2 : ∃ d, 1 / y = 1 / x + d ∧ 1 / z = 1 / y + d) :
    x / z + z / x = 34 / 15 := by
  rcases h1 with ⟨r, h11, h12⟩
  rcases h2 with ⟨d, h21, h22⟩
  have h3 : 16 * y ^ 2 = 15 * x * z := by
    have eq1 : 4 * y = 3 * x * r := by linarith
    have eq2 : 5 * z = 4 * y * r := by linarith
    have eq3 : 16 * y ^ 2 = 9 * x ^ 2 * r ^ 2 := by
      have hy_eq : y = (3 * x * r) / 4 := by
        linarith
      rw [hy_eq]
      nlinarith
    have eq4 : 15 * x * z = 9 * x ^ 2 * r ^ 2 := by
      have h12' : 5 * z = 4 * y * r := by linarith
      have h11' : 4 * y = 3 * x * r := by linarith
      rw [h11'] at h12'
      have hz_eq : z = (3 * x * r ^ 2) / 5 := by
        nlinarith
      rw [hz_eq]
      nlinarith
    nlinarith
  have h4 : 2 * x * z = x * y + y * z := by
    have eq3 : 2 * (1 / y) = 1 / x + 1 / z := by
      have eq1 : 1 / y = 1 / x + d := by linarith
      have eq2 : 1 / z = 1 / y + d := by linarith
      nlinarith
    have eq4 : 2 * x * z = x * y + y * z := by
      field_simp [hy, hx, hz] at eq3 ⊢
      nlinarith
    linarith
  have h5 : x / z + z / x = (x ^ 2 + z ^ 2) / (x * z) := by
    field_simp [hz, hx]
    <;> ring
  have h6 : x ^ 2 + z ^ 2 = 34 / 15 * (x * z) := by
    nlinarith [sq_nonneg (y ^ 2), sq_nonneg (x * z), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_pos_of_ne_zero hz, sq_nonneg (x - z)]
  have h7 : (x ^ 2 + z ^ 2) / (x * z) = 34 / 15 := by
    have h8 : x * z ≠ 0 := by
      apply mul_ne_zero
      exact hx
      exact hz
    field_simp [h8]
    nlinarith [h6]
  rw [h5]
  linarith [h7]