import Mathlib

theorem algebra_10949 {x y z k : ℝ} (h₀ : x + y ≠ 0 ∧ x + z ≠ 0 ∧ z - y ≠ 0)
  (h : 7 / (x + y) = k / (x + z) ∧ k / (x + z) = 11 / (z - y)) :
  k = 18 := by
  rcases h₀ with ⟨hxy, hxz, hyz⟩
  rcases h with ⟨h1, h2⟩

  have eq1 : 7 * (x + z) = k * (x + y) := by
    have h1' : 7 / (x + y) = k / (x + z) := h1
    field_simp [hxy, hxz] at h1'
    linarith

  have eq2 : k * (z - y) = 11 * (x + z) := by
    have h2' : k / (x + z) = 11 / (z - y) := h2
    field_simp [hxz, hyz] at h2'
    linarith

  have eq3 : 7 * (z - y) = 11 * (x + y) := by
    have h3 : k = 7 * (x + z) / (x + y) := by
      have : 7 * (x + z) = k * (x + y) := eq1
      field_simp [hxy] at *
      linarith
    have eq2_rw : 7 * (x+z) * (z - y) = 11 * (x+z) * (x + y) := by
      have eq2' : k * (z - y) = 11 * (x + z) := eq2
      rw [h3] at eq2'
      field_simp [hxy, hxz] at eq2'
      <;> nlinarith
    have hxz' : x + z ≠ 0 := hxz
    apply (mul_right_inj' hxz').mp
    linarith [eq2_rw]

  have eq4 : 18 * (x + y) = k * (x + y) := by
    have h5 : 7 * z = 11 * x + 18 * y := by
      linarith [eq3]
    have eq1' : 7 * (x + z) = k * (x + y) := eq1
    have eq1_rw : 7 * (x + z) = 18 * (x + y) := by
      have h5' : 7 * z = 11 * x + 18 * y := h5
      nlinarith
    have eq2_rw : k * (x + y) = 18 * (x + y) := by
      nlinarith [eq1', eq1_rw]
    linarith

  have eq5 : (k - 18) * (x + y) = 0 := by
    have eq4_rw : 18 * (x + y) = k * (x + y) := eq4
    nlinarith

  cases' (mul_eq_zero.mp eq5) with h7 h8
  · -- Case k - 18 = 0
    linarith
  · -- Case x + y = 0
    exfalso
    exact hxy (by linarith)