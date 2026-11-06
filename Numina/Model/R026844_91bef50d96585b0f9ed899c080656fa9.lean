import Mathlib

theorem algebra_250028 {x y z : ℝ} (h₀ : x ≠ -y) (h₁ : x ≠ -z) (h₂ : y ≠ -z)
    (h₃ : 3 * x * y / (x + y) = 5) (h₄ : 2 * x * z / (x + z) = 3) (h₅ : y * z / (y + z) = 4) :
    x = 120 / 61 ∧ y = 120 / 11 ∧ z = 120 / 19 := by

  have h₆ : x + y ≠ 0 := by
    by_contra h
    have : x = -y := by linarith
    contradiction

  have h₇ : x + z ≠ 0 := by
    by_contra h
    have : x = -z := by linarith
    contradiction

  have h₈ : y + z ≠ 0 := by
    by_contra h
    have : y = -z := by linarith
    contradiction

  have eq1 : 3 * x * y = 5 * (x + y) := by
    have h6 : x + y ≠ 0 := h₆
    field_simp [h6] at h₃ ⊢
    linarith

  have eq2 : 2 * x * z = 3 * (x + z) := by
    have h7 : x + z ≠ 0 := h₇
    field_simp [h7] at h₄ ⊢
    linarith

  have eq3 : y * z = 4 * (y + z) := by
    have h8 : y + z ≠ 0 := h₈
    field_simp [h8] at h₅ ⊢
    linarith

  have h₉ : x ≠ 0 := by
    by_contra h
    have eq1' : 3 * x * y = 5 * (x + y) := eq1
    have eq2' : 2 * x * z = 3 * (x + z) := eq2
    rw [h] at eq1' eq2'
    have hy : y = 0 := by
      nlinarith
    have hz : z = 0 := by
      nlinarith
    have h_yz_zero : y + z = 0 := by
      linarith [hy, hz]
    exfalso
    exact h₈ h_yz_zero

  have h₁₀ : y ≠ 0 := by
    by_contra h
    have eq1' : 3 * x * y = 5 * (x + y) := eq1
    have eq3' : y * z = 4 * (y + z) := eq3
    rw [h] at eq1' eq3'
    have hx : x = 0 := by
      nlinarith
    have hz : z = 0 := by
      nlinarith
    have h_xz_zero : x + z = 0 := by
      linarith [hx, hz]
    exfalso
    exact h₇ h_xz_zero

  have h₁₁ : z ≠ 0 := by
    by_contra h
    have eq2' : 2 * x * z = 3 * (x + z) := eq2
    have eq3' : y * z = 4 * (y + z) := eq3
    rw [h] at eq2' eq3'
    have hx : x = 0 := by
      nlinarith
    have hy : y = 0 := by
      nlinarith
    have h_xy_zero : x + y = 0 := by
      linarith [hx, hy]
    exfalso
    exact h₆ h_xy_zero

  have eq_a : 5 * (1 / x + 1 / y) = 3 := by
    have h1 : x ≠ 0 := h₉
    have h2 : y ≠ 0 := h₁₀
    field_simp [h1, h2] at eq1 ⊢
    linarith

  have eq_b : 3 * (1 / x + 1 / z) = 2 := by
    have h1 : x ≠ 0 := h₉
    have h2 : z ≠ 0 := h₁₁
    field_simp [h1, h2] at eq2 ⊢
    linarith

  have eq_c : 4 * (1 / y + 1 / z) = 1 := by
    have h1 : y ≠ 0 := h₁₀
    have h2 : z ≠ 0 := h₁₁
    field_simp [h1, h2] at eq3 ⊢
    linarith

  have ha : 1 / x = 61 / 120 := by
    have eq_a' : 5 * (1 / x + 1 / y) = 3 := eq_a
    have eq_b' : 3 * (1 / x + 1 / z) = 2 := eq_b
    have eq_c' : 4 * (1 / y + 1 / z) = 1 := eq_c
    linarith [eq_a', eq_b', eq_c']

  have hb : 1 / y = 11 / 120 := by
    have eq_a' : 5 * (1 / x + 1 / y) = 3 := eq_a
    have eq_b' : 3 * (1 / x + 1 / z) = 2 := eq_b
    have eq_c' : 4 * (1 / y + 1 / z) = 1 := eq_c
    linarith [eq_a', eq_b', eq_c']

  have hc : 1 / z = 19 / 120 := by
    have eq_a' : 5 * (1 / x + 1 / y) = 3 := eq_a
    have eq_b' : 3 * (1 / x + 1 / z) = 2 := eq_b
    have eq_c' : 4 * (1 / y + 1 / z) = 1 := eq_c
    linarith [eq_a', eq_b', eq_c']

  have hx : x = 120 / 61 := by
    have h1 : 1 / x = 61 / 120 := ha
    have h2 : x ≠ 0 := h₉
    field_simp [h2] at h1 ⊢
    <;> linarith

  have hy : y = 120 / 11 := by
    have h1 : 1 / y = 11 / 120 := hb
    have h2 : y ≠ 0 := h₁₀
    field_simp [h2] at h1 ⊢
    <;> linarith

  have hz : z = 120 / 19 := by
    have h1 : 1 / z = 19 / 120 := hc
    have h2 : z ≠ 0 := h₁₁
    field_simp [h2] at h1 ⊢
    <;> linarith

  exact ⟨hx, hy, hz⟩