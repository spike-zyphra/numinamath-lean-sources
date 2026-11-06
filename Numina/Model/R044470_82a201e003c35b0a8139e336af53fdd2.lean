import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_112295
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  3 / 2 ≤ (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) +
    (a + b) / (a + b + 2 * c) ∧
  (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) +
    (a + b) / (a + b + 2 * c) < 5 / 3 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  constructor
  · -- Proof of the lower bound: $\frac{3}{2} \leq \frac{b+c}{b+c+2a}+\frac{a+c}{a+c+2b}+\frac{a+b}{a+b+2c}$
    have h4 : (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) + (a + b) / (a + b + 2 * c) ≥ 3 / 2 := by
      have h6 : (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) + (a + b) / (a + b + 2 * c) - 3 / 2 ≥ 0 := by
        have h7 : (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) + (a + b) / (a + b + 2 * c) - 3 / 2 =
            ((b + c) * (a + c + 2 * b) * (a + b + 2 * c) +
            (a + c) * (b + c + 2 * a) * (a + b + 2 * c) +
            (a + b) * (b + c + 2 * a) * (a + c + 2 * b) - 3/2 * (b + c + 2 * a) * (a + c + 2 * b) * (a + b + 2 * c))
            / ((b + c + 2 * a) * (a + c + 2 * b) * (a + b + 2 * c)) := by
          field_simp
          ring
        rw [h7]
        apply div_nonneg
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
        positivity
      linarith
    linarith
  · -- Proof of the upper bound: $ \frac{b+c}{b+c+2a}+\frac{a+c}{a+c+2b}+\frac{a+b}{a+b+2c} < \frac{5}{3}$
    have h4 : (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) + (a + b) / (a + b + 2 * c) < 5 / 3 := by
      have h6 : (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) + (a + b) / (a + b + 2 * c) - 5 / 3 < 0 := by
        have h7 : (b + c) / (b + c + 2 * a) + (a + c) / (a + c + 2 * b) + (a + b) / (a + b + 2 * c) - 5 / 3 =
            ((b + c) * (a + c + 2 * b) * (a + b + 2 * c) +
            (a + c) * (b + c + 2 * a) * (a + b + 2 * c) +
            (a + b) * (b + c + 2 * a) * (a + c + 2 * b) - 5/3 * (b + c + 2 * a) * (a + c + 2 * b) * (a + b + 2 * c))
            / ((b + c + 2 * a) * (a + c + 2 * b) * (a + b + 2 * c)) := by
          field_simp
          ring
        rw [h7]
        apply div_neg_of_neg_of_pos
        · 
          nlinarith [sq_pos_of_pos (show 0 < a by linarith), sq_pos_of_pos (show 0 < b by linarith), sq_pos_of_pos (show 0 < c by linarith),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
            mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
            mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
            mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁)
            ]
        · 
          positivity
      linarith
    linarith