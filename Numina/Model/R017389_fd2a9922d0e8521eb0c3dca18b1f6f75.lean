import Mathlib.Tactic

theorem inequalities_597753
    (x y z : ℝ)
    (h₀ : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z)
    (h₁ : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 :=
  by 
  constructor 
  · -- Show $0 \leq x * y + y * z + z * x - 2 * x * y * z$
    have hx0 : 0 ≤ x := h₀.1 
    have hy0 : 0 ≤ y := h₀.2.1 
    have hz0 : 0 ≤ z := h₀.2.2 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_nonneg hx0 hy0, mul_nonneg hx0 hz0, mul_nonneg hy0 hz0
      ]
  · -- Show x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27
    have hx0 : 0 ≤ x := h₀.1 
    have hy0 : 0 ≤ y := h₀.2.1 
    have hz0 : 0 ≤ z := h₀.2.2 
    have h3 : x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
      have h4 : z = 1 - x - y := by linarith
      rw [h4]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
          sq_nonneg (x + y - (1 - x - y)), mul_nonneg hx0 hy0, 
          mul_nonneg hx0 (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
          mul_nonneg hy0 (show 0 ≤ (1 - x - y : ℝ) by nlinarith)
        ]
    linarith