import Mathlib

open Real

theorem algebra_14485 :
  IsGreatest {logb a (a / b) + logb b (b / a) | (a : ℝ) (b : ℝ) (_ : a ≥ b ∧ b > 1)} 0 := by
  constructor
  · -- Show 0 is in the set.
    use 2, 2, ⟨by norm_num, by norm_num⟩
    have h1 : logb (2 : ℝ) (2 / 2) = logb (2 : ℝ) 1 := by
      norm_num
    have h2 : logb (2 : ℝ) 1 = (0 : ℝ) := by
      norm_num [logb_one]
    rw [h1, h2]
    all_goals norm_num [h2]
  · -- Show that 0 is greatest in the set
    intro x hx
    rcases hx with ⟨a, b, ⟨ha1, hb⟩, h⟩
    have h1 : logb a (a / b) = logb a a - logb a b := by 
      rw [logb_div (by linarith) (by linarith)]
    have h2 : logb b (b / a) = logb b b - logb b a := by 
      rw [logb_div (by linarith) (by linarith)]
    have h3 : logb a a = (1 : ℝ) := by 
      rw [logb_self_eq_one]
      all_goals linarith
    have h4 : logb b b = (1 : ℝ) := by 
      rw [logb_self_eq_one]
      all_goals linarith
    rw [h1, h2, h3, h4] at h
    have h7 : logb a b + logb b a ≥ (2 : ℝ) := by
      have h5 : logb a b = (log b) / (log a) := by 
        field_simp [logb]
      have h6 : logb b a = (log a) / (log b) := by 
        field_simp [logb]
      rw [h5, h6]
      have h8 : log b > (0 : ℝ) := by
        apply log_pos
        linarith
      have h9 : log a > (0 : ℝ) := by
        apply log_pos
        linarith
      have h10 : (log b) / (log a) + (log a) / (log b) ≥ 2 := by
        have h11 : log b > 0 := h8
        have h12 : log a > 0 := h9
        have h13 : (log b) / (log a) + (log a) / (log b) - (2 : ℝ) ≥ 0 := by
          have eq1 : (log b) / (log a) + (log a) / (log b) - (2 : ℝ) = ((log b) ^ 2 + (log a) ^ 2 - 2 * (log a) * (log b)) / ((log a) * (log b)) := by
            field_simp
            <;> ring
          rw [eq1]
          have h14 : (log b) ^ 2 + (log a) ^ 2 - 2 * (log a) * (log b) ≥ 0 := by
            have h16 : (log b - log a) ^ 2 ≥ 0 := sq_nonneg (log b - log a)
            linarith
          have h15 : (log a) * (log b) > 0 := mul_pos h9 h8
          apply div_nonneg h14 (by positivity)
        linarith
      linarith
    linarith