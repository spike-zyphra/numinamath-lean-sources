import Mathlib

theorem algebra_242838 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : (a + b) / (a * b) = 1) (h2 : (b + c) / (b * c) = 1 / 2)
    (h3 : (c + a) / (c * a) = 1 / 4) :
    a = 8 / 3 ∧ b = 8 / 5 ∧ c = -8 := by
  have eq1 : 1 / a + 1 / b = 1 := by
    have h1' : (a + b) / (a * b) = 1 := h1
    have : (a + b) / (a * b) = 1 / a + 1 / b := by
      field_simp [show a ≠ 0 by assumption, show b ≠ 0 by assumption]
      <;> ring
    linarith [this, h1']
  have eq2 : 1 / b + 1 / c = 1 / 2 := by
    have h2' : (b + c) / (b * c) = 1 / 2 := h2
    have : (b + c) / (b * c) = 1 / b + 1 / c := by
      field_simp [show b ≠ 0 by assumption, show c ≠ 0 by assumption]
      <;> ring
    linarith [this, h2']
  have eq3 : 1 / c + 1 / a = 1 / 4 := by
    have h3' : (c + a) / (c * a) = 1 / 4 := h3
    have : (c + a) / (c * a) = 1 / c + 1 / a := by
      field_simp [show c ≠ 0 by assumption, show a ≠ 0 by assumption]
      <;> ring
    linarith [this, h3']
  have h1a : 1 / a = 3 / 8 := by
    linarith [eq1, eq2, eq3]
  have h1b : a = 8 / 3 := by
    have hne : a ≠ 0 := ha
    field_simp at h1a ⊢
    <;> linarith
  have h2b : 1 / b = 5 / 8 := by
    linarith [eq1, eq2, eq3]
  have h2c : b = 8 / 5 := by
    have hne : b ≠ 0 := hb
    field_simp at h2b ⊢
    <;> linarith
  have h3c : 1 / c = -1 / 8 := by
    linarith [eq1, eq2, eq3]
  have h3d : c = -8 := by
    have hne : c ≠ 0 := hc
    field_simp at h3c ⊢
    <;> linarith
  exact ⟨h1b, h2c, h3d⟩