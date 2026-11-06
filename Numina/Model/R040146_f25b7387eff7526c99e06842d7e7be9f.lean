import Mathlib

theorem algebra_156745 {x y z a b c : ℝ} (h₀ : x * y = a) (h₁ : x * z = b)
    (h₂ : y * z = c) (h₃ : a ≠ 0) (h₄ : b ≠ 0) (h₅ : c ≠ 0) :
    x^2 + y^2 + z^2 = ((a * b)^2 + (a * c)^2 + (b * c)^2) / (a * b * c) := by

  have hx2 : x^2 = (a * b) / c := by
    have h3 : x^2 = (x * y) * (x * z) / (y * z) := by
      field_simp [(show y * z ≠ 0 by
        intro h'
        apply h₅
        linarith)]
      <;> ring
    rw [h₀, h₁, h₂] at h3
    linarith

  have hy2 : y^2 = (a * c) / b := by
    have h4 : y^2 = (x * y) * (y * z) / (x * z) := by
      field_simp [(show x * z ≠ 0 by
        intro h'
        apply h₄
        linarith)]
      <;> ring
    rw [h₀, h₁, h₂] at h4
    linarith

  have hz2 : z^2 = (b * c) / a := by
    have h5 : z^2 = (x * z) * (y * z) / (x * y) := by
      field_simp [(show x * y ≠ 0 by
        intro h'
        apply h₃
        linarith)]
      <;> ring
    rw [h₀, h₁, h₂] at h5
    linarith

  have eq : x^2 + y^2 + z^2 = (a * b / c) + (a * c / b) + (b * c / a) := by
    linarith [hx2, hy2, hz2]

  rw [eq]
  field_simp [(show a ≠ 0 by exact h₃), (show b ≠ 0 by exact h₄), (show c ≠ 0 by exact h₅)]
  <;> ring