import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_598819
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : a + c > b)
  (h₃ : b + c > a) :
  (-a + b + c) * (a - b + c) + (a - b + c) * (a + b - c) +
  (a + b - c) * (-a + b + c) ≤
  Real.sqrt (a * b * c) * (Real.sqrt a + Real.sqrt b + Real.sqrt c) := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have h4 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h5 : Real.sqrt a ≥ 0 := by positivity
  have h6 : Real.sqrt b ≥ 0 := by positivity
  have h7 : Real.sqrt c ≥ 0 := by positivity
  have h8 : Real.sqrt (a * b * c) = Real.sqrt a * Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  rw [h8]
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c, 
          mul_nonneg (show 0 ≤ Real.sqrt a by positivity) (show 0 ≤ Real.sqrt b by positivity),
          mul_nonneg (show 0 ≤ Real.sqrt a by positivity) (show 0 ≤ Real.sqrt c by positivity),
          mul_nonneg (show 0 ≤ Real.sqrt b by positivity) (show 0 ≤ Real.sqrt c by positivity),
          sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - Real.sqrt c), sq_nonneg (Real.sqrt b - Real.sqrt c),
          Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), Real.sq_sqrt (show 0 ≤ c by linarith),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr (show a + b > c by linarith)) (sub_pos.mpr (show a + c > b by linarith)), 
          mul_pos (sub_pos.mpr (show a + c > b by linarith)) (sub_pos.mpr (show b + c > a by linarith)), 
          mul_pos (sub_pos.mpr (show b + c > a by linarith)) (sub_pos.mpr (show a + b > c by linarith))
    ]