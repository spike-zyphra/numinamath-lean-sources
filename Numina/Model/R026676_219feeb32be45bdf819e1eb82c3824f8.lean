import Mathlib

theorem inequalities_600119 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 / (a * b + b * c + c * a) < 1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) +
    1 / (c ^ 2 + 2 * a * b) := by 
  have h1 : 0 < a * b + b * c + c * a := by positivity
  have h2 : 0 < a ^ 2 + 2 * b * c := by positivity
  have h3 : 0 < b ^ 2 + 2 * c * a := by positivity
  have h4 : 0 < c ^ 2 + 2 * a * b := by positivity

  have h5 : (1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) + 1 / (c ^ 2 + 2 * a * b) ) - 2 / (a * b + b * c + c * a) > 0 := by
    have hx1 : 0 < (a ^ 2 + 2 * b * c) := by positivity
    have hy1 : 0 < (b ^ 2 + 2 * c * a) := by positivity
    have hz1 : 0 < (c ^ 2 + 2 * a * b) := by positivity
    have hxyz : 0 < (a * b + b * c + c * a) := by positivity
  
    have h5' : (1 / (a ^ 2 + 2 * b * c) + 1 / (b ^ 2 + 2 * c * a) + 1 / (c ^ 2 + 2 * a * b) ) - 2 / (a * b + b * c + c * a) =
        ((b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) * (a * b + b * c + c * a) + (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) * (a * b + b * c + c * a) + (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (a * b + b * c + c * a) - 2 * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) / ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) * (a * b + b * c + c * a)) := by
      field_simp
      <;> ring
    rw [h5'] at *
    have h6 : 0 < (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) * (a * b + b * c + c * a) := by positivity
    have h7 : ((b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) * (a * b + b * c + c * a) + (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) * (a * b + b * c + c * a) + (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (a * b + b * c + c * a) - 2 * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) > 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
          sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (a - c)),
          sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), sq_nonneg (c * (a - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
          mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
          mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    apply div_pos
    linarith
    all_goals positivity
  linarith