import Mathlib

theorem algebra_7234 {x y z k : ℝ} (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) (h1 : (x + 2 * y) / z = k) (h2 : (y + 2 * z) / x = k) (h3 : (z + 2 * x) / y = k) :
    k = 3 := by 
  rcases h with ⟨hx, hy, hz⟩ 
  have eq1 : x + 2 * y = k * z := by
    have h1' : (x + 2 * y) / z = k := h1
    field_simp [hz] at h1' ⊢
    linarith
  have eq2 : y + 2 * z = k * x := by
    have h2' : (y + 2 * z) / x = k := h2
    field_simp [hx] at h2' ⊢
    linarith
  have eq3 : z + 2 * x = k * y := by
    have h3' : (z + 2 * x) / y = k := h3
    field_simp [hy] at h3' ⊢
    linarith
  have eq4 : 3 * (x + y + z) = k * (x + y + z) := by
    nlinarith [eq1, eq2, eq3]
  by_cases h4 : x + y + z = 0
  · -- Case where x + y + z = 0, derive a contradiction.
    have h4' : z = -x - y := by linarith
    rw [h4'] at eq1
    have eq5 : x * (1 + k) + y * (2 + k) = 0 := by 
      nlinarith
    rw [h4'] at eq2
    have eq6 : x * (-2 - k) - y = 0 := by 
      nlinarith
    have eq7 : x = y * (1 + k) := by
      nlinarith [eq6]
    rw [eq7] at eq6 
    have hk : k ^ 2 + 3 * k + 3 = 0 := by
      apply (mul_left_inj' hy).mp 
      nlinarith 
    nlinarith [sq_nonneg (k + 3 / 2)]
  · -- Case where x + y + z ≠ 0, so k = 3
    have hk : k = 3 := by
      apply (mul_left_inj' h4).mp 
      nlinarith
    exact_mod_cast hk