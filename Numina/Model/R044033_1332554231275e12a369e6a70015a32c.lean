import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_142677
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : a + c > b)
  (h₃ : b + c > a) :
  a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 ∧
  (a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) = 0 ↔
    (a = b ∧ b = c)) := by
  constructor
  · -- Prove that a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0
    have h1 : 0 < a := h₀.1
    have h2 : 0 < b := h₀.2.1
    have h3 : 0 < c := h₀.2.2
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃)
    ]
  · -- Determine when equality occurs
    constructor
    · -- Assume the equality holds, prove a = b and b = c
      intro heq
      have h1 : 0 < a := h₀.1
      have h2 : 0 < b := h₀.2.1
      have h3 : 0 < c := h₀.2.2
      have h4 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3,
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃)
        ]
      have h5 : a - b = 0 := by
        nlinarith
      have h6 : a = b := by linarith
      have h7 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos h1 h2, mul_pos h2 h3, mul_pos h1 h3,
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂),
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃)
        ]
      have h8 : b - c = 0 := by
        nlinarith
      have h9 : b = c := by linarith
      exact ⟨h6, h9⟩
    · -- Assume a = b and b = c, prove the equality
      rintro ⟨ha, hb⟩
      have h4 : a = c := by linarith
      rw [show b = a by linarith [ha], show c = a by linarith [h4]]
      ring_nf