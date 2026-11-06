import Mathlib

theorem algebra_610208 (x y z : ℝ) (h₁ : x * y = 6) (h₂ : x - z = 2) (h₃ : x + y + z = 9) :
    x / y - z / x - z ^ 2 / (x * y) = 2 := by
  have hz : z = x - 2 := by
    linarith
  have h₄ : 2 * x + y = 11 := by
    have h₅ : z = x - 2 := hz
    rw [h₅] at h₃
    linarith
  have h₅ : x ≠ 0 := by
    by_contra hx
    have h6 : x * y = 0 := by
      rw [hx]
      norm_num
    linarith [h₁, h6]
  have h₆ : y ≠ 0 := by
    by_contra hy
    have h7 : x * y = 0 := by
      rw [hy
      ]
      norm_num
    linarith [h₁, h7]
  have h₇ : x / y - z / x - z ^ 2 / (x * y) = (x^2 - z * y - z^2) / (x * y) := by
    have hx : x ≠ 0 := h₅
    have hy : y ≠ 0 := h₆
    field_simp
    <;> ring
  rw [h₇
  ]
  rw [hz
  ]
  have h₈ : x * y = 6 := h₁
  have h₉ : x * y = 6 := h₁
  have h₁₀ : x^2 - (x - 2) * y - (x - 2)^2 = 12 := by
    have h₄ : 2 * x + y = 11 := h₄
    have h₉ : x * y = 6 := h₁
    nlinarith
  field_simp [h₉, h₆, h₅
  ]
  <;> nlinarith [h₁₀, h₈
  ]