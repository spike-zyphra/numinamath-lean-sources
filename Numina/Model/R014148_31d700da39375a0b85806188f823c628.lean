import Mathlib

open Real

theorem inequalities_3327 :
  IsLeast {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = (1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a))} (27 / 8) := by 
  constructor 
  · -- Show 27/8 is in the set 
    use 2, 2, 2 
    norm_num 
  · -- Show that it is a lower bound 
    intro x hx 
    rcases hx with ⟨a, b, c, ha, hb, hc, hx⟩
    have h2 : (1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a)) ≥ 27 / 8 := by 
      have h12 : 0 < a * b * c := by positivity 
      have h1 : 8 * a * b * c * ((1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a))) - 27 * a * b * c ≥ 0 := by
        have h2 : 8 * a * b * c * ((1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a))) =
            (2 * b + a) * (2 * c + b) * (2 * a + c) := by 
          field_simp 
          <;> ring 
        rw [h2]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)
          ]
      have h16 : (8 * a * b * c * ((1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a))) - 27 * a * b * c) / (8 * a * b * c) ≥ 0 := by
        apply div_nonneg 
        linarith [h1] 
        all_goals positivity 
      have eq1 : (1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a)) - 27 / 8 =
          (8 * a * b * c * ((1 + a / (2 * b)) * (1 + b / (2 * c)) * (1 + c / (2 * a)) ) - 27 * a * b * c ) / (8 * a * b * c) := by
        field_simp 
        <;> ring 
      linarith [eq1, h16]
    linarith [hx, h2]