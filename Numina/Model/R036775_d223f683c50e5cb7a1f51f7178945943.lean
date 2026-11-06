import Mathlib

theorem algebra_1274 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (h : ∃ k, 1 / x + 1 / y = k / (x + y)) :
    ∃ m, (x + y) ^ 2 = m * (x ^ 2 + y ^ 2) := by
  rcases h with ⟨k, hk⟩
  have eq1 : 1 / x + 1 / y = (x + y) / (x * y) := by
    field_simp [hx, hy]
    <;> ring
  have eq2 : (x + y) / (x * y) = k / (x + y) := by
    linarith [eq1, hk]
  have eq3 : (x + y) ^ 2 = k * (x * y) := by 
    have h1 : x * y ≠ 0 := mul_ne_zero hx hy
    have h2 : x + y ≠ 0 := hxy
    field_simp [h1, h2] at eq2
    nlinarith 
  by_cases h_k : k = 2
  · -- Assume k = 2 
    have eq4 : (x + y) ^ 2 = 2 * (x * y) := by
      rw [h_k] at eq3
      linarith 
    have eq5 : x ^ 2 + y ^ 2 = 0 := by
      nlinarith 
    have hx2 : x ^ 2 > 0 := by
      apply sq_pos_of_ne_zero 
      exact hx
    have hy2 : y ^ 2 > 0 := by
      apply sq_pos_of_ne_zero 
      exact hy
    linarith 
  · -- Assume k ≠ 2 
    use (k / (k - 2 : ℝ))
    have h_k2 : k - 2 ≠ 0 := by 
      intro h'
      have h_k_eq : k = 2 := by linarith 
      tauto 
    have eq6 : x ^ 2 + y ^ 2 = (k - 2) * (x * y) := by 
      have eq4 : (x + y) ^ 2 = k * (x * y) := eq3 
      nlinarith 
    have eq7 : (k / (k - 2)) * (x ^ 2 + y ^ 2) = k * (x * y) := by 
      rw [eq6]
      field_simp [h_k2] 
      <;> ring 
    linarith [eq3, eq7]