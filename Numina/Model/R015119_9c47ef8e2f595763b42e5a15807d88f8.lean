import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_192665 (A B C : EuclideanSpace ℝ (Fin 2))
    (a b c : ℝ)
    (ha : a = dist B C)
    (hb : b = dist A C)
    (hc : c = dist A B)
    (h : 0 < a ∧ 0 < b ∧ 0 < c) :
    3 < (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) +
        (c^2 + 2 * a * b) / (a^2 + b^2) := by 
  rcases h with ⟨ha1, hb1, hc1⟩
  have h4 : 0 < b^2 + c^2 := by positivity
  have h5 : 0 < c^2 + a^2 := by positivity
  have h6 : 0 < a^2 + b^2 := by positivity
  have h1 : (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) + (c^2 + 2 * a * b) / (a^2 + b^2) - 3 > 0 := by
    have h9 : (a^2 + 2 * b * c) / (b^2 + c^2) + (b^2 + 2 * a * c) / (c^2 + a^2) + (c^2 + 2 * a * b) / (a^2 + b^2) - 3 =
        ((a^2 + 2 * b * c) * (c^2 + a^2) * (a^2 + b^2) + (b^2 + 2 * a * c) * (b^2 + c^2) * (a^2 + b^2) + (c^2 + 2 * a * b) * (b^2 + c^2) * (c^2 + a^2) - 3 * (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) / ((b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) := by 
      field_simp
      <;> ring 
    rw [h9] at *
    have h10 : (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2) > 0 := by positivity
    have hx5 : ((a^2 + 2 * b * c) * (c^2 + a^2) * (a^2 + b^2) + (b^2 + 2 * a * c) * (b^2 + c^2) * (a^2 + b^2) + (c^2 + 2 * a * b) * (b^2 + c^2) * (c^2 + a^2) - 3 * (b^2 + c^2) * (c^2 + a^2) * (a^2 + b^2)) > 0 := by 
      nlinarith [mul_pos ha1 hb1, mul_pos ha1 hc1, mul_pos hb1 hc1, mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity), mul_pos (show 0 < a * b from by positivity) (show 0 < a * c from by positivity), mul_pos (show 0 < a * c from by positivity) (show 0 < b * c from by positivity), sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (b * c - a * c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg ((a - b) * (a - c)), sq_nonneg ((a - b) * (b - c)), sq_nonneg ((a - c) * (b - c)), mul_pos ha1 (show 0 < a^2 from by positivity), mul_pos hb1 (show 0 < b^2 from by positivity), mul_pos hc1 (show 0 < c^2 from by positivity)]
    apply div_pos 
    linarith 
    all_goals 
      positivity
  linarith
  all_goals 
    try positivity