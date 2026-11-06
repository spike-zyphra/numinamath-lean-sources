import Mathlib

theorem algebra_202602 {x y z : ℝ} (h1 : x * y = 1) (h2 : y * z = 2) (h3 : z * x = 8) :
    (x = 2 ∧ y = 1 / 2 ∧ z = 4) ∨ (x = -2 ∧ y = -1 / 2 ∧ z = -4) := by
  have h4 : (x * y * z) ^ 2 = 16 := by
    calc
      (x * y * z) ^ 2 = (x * y) * (y * z) * (z * x) := by ring
      _ = 1 * 2 * 8 := by rw [h1, h2, h3]
      _ = 16 := by norm_num
  have h5 : x * y * z = 4 ∨ x * y * z = -4 := by
    have h6 : (x * y * z) ^ 2 - 16 = 0 := by linarith
    have h7 : (x * y * z - 4) * (x * y * z + 4) = 0 := by
      linarith [h6]
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      left
      linarith
    | inr h9 =>
      right
      linarith
  cases h5 with
  | inl h5l =>
    have h4 : z = 4 := by
      have h5 : x * y * z = 4 := h5l
      have hxy : x * y = 1 := h1
      have : z = (x * y * z) / (x * y) := by
        field_simp [hxy]
        <;> nlinarith
      rw [h5, hxy] at this
      linarith
    have hy : y = 1 / 2 := by
      have h5 : x * y * z = 4 := h5l
      have h2' : y * z = 2 := h2
      have hz : z = 4 := h4
      have : y = (y * z) / z := by
        field_simp [hz]
        <;> nlinarith
      rw [h2', hz] at this
      linarith
    have hx : x = 2 := by
      have h5 : x * y * z = 4 := h5l
      have h1' : x * y = 1 := h1
      have hy' : y = 1 / 2 := hy
      have : x = (x * y) / y := by
        field_simp [hy']
        <;> nlinarith
      rw [h1', hy'] at this
      linarith
    left
    exact ⟨hx, hy, h4⟩
  | inr h5r =>
    have h4 : z = -4 := by
      have h5 : x * y * z = -4 := h5r
      have hxy : x * y = 1 := h1
      have : z = (x * y * z) / (x * y) := by
        field_simp [hxy]
        <;> nlinarith
      rw [h5, hxy] at this
      linarith
    have hy : y = -1 / 2 := by
      have h5 : x * y * z = -4 := h5r
      have h2' : y * z = 2 := h2
      have hz : z = -4 := h4
      have : y = (y * z) / z := by
        field_simp [hz]
        <;> nlinarith
      rw [h2', hz] at this
      linarith
    have hx : x = -2 := by
      have h5 : x * y * z = -4 := h5r
      have h1' : x * y = 1 := h1
      have hy' : y = -1 / 2 := hy
      have : x = (x * y) / y := by
        field_simp [hy']
        <;> nlinarith
      rw [h1', hy'] at this
      linarith
    right
    exact ⟨hx, hy, h4⟩