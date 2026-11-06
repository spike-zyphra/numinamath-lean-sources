import Mathlib

theorem inequalities_300055
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b * c = 1) :
    4 ≤ 1 / a + 1 / b + 1 / c + 3 / (a + b + c) := by

  have h5 : 1 / a + 1 / b + 1 / c = (a * b + a * c + b * c) / (a * b * c) := by
    field_simp
    <;> ring
  rw [h5]
  rw [show a * b * c = 1 by linarith [h₃]]
  have h7 : a + b + c ≥ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, h₃
    ]
  have h8 : (a * b + a * c + b * c) + 3 / (a + b + c) ≥ 4 := by
    have h9 : (a * b + a * c + b * c) + 3 / (a + b + c) - 4 ≥ 0 := by
      have pos1 : 0 < a + b + c := by
        linarith [h₀, h₁, h₂]
      have h14 : ( (a * b + a * c + b * c ) + 3 / (a + b + c ) - 4 ) = ( ( (a * b + a * c + b * c ) * (a + b + c ) + 3 - 4 * (a + b + c ) ) ) / (a + b + c ) := by
        field_simp
        <;> ring
      rw [h14]
      have h10 : ( (a * b + a * c + b * c ) * (a + b + c ) + 3 - 4 * (a + b + c ) ) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h₃, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂
        ]
      apply div_nonneg h10 (by linarith)
    linarith
  nlinarith [h8, h₃, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]