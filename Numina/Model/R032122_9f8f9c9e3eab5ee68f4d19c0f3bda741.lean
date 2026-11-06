import Mathlib

open Real

lemma my_ineq (x : ℝ) (hx : 0 < x) : (x ^ 2 / (x + 2)) + 2 / 3 ≥ 5 / 9 * x + 4 / 9 := by
  have h1 : 0 < x + 2 := by linarith
  have h2 : (x ^ 2 / (x + 2)) + 2 / 3 ≥ 5 / 9 * x + 4 / 9 := by
    have h3 : (x ^ 2 / (x + 2)) + 2 / 3 - (5 / 9 * x + 4 / 9) ≥ 0 := by
      have h4 : (x ^ 2 / (x + 2)) + 2 / 3 - (5 / 9 * x + 4 / 9) = 
        (9 * x ^ 2 + 6 * (x + 2) - 5 * x * (x + 2) - 4 * (x + 2)) / (9 * (x + 2)) := by 
        field_simp
        ring 
      rw [h4]
      have h5 : 9 * (x + 2) > 0 := by
        nlinarith
      have h8 : (9 * x ^ 2 + 6 * (x + 2) - 5 * x * (x + 2) - 4 * (x + 2)) ≥ (0 : ℝ) := by
        nlinarith [sq_nonneg (x - 1)]
      apply div_nonneg 
      all_goals 
        nlinarith 
    linarith 
  linarith 
theorem inequalities_1170 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / (a + 2) + b ^ 2 / (b + 2) + c ^ 2 / (c + 2) + 2 / 3 ≥ 5 / 9 * (a + b + c) := by 
  have h_a : (a ^ 2 / (a + 2)) + 2 / 3 ≥ 5 / 9 * a + 4 / 9 := by 
    apply my_ineq a ha 
  have h_b : (b ^ 2 / (b + 2)) + 2 / 3 ≥ 5 / 9 * b + 4 / 9 := by 
    apply my_ineq b hb 
  have h_c : (c ^ 2 / (c + 2)) + 2 / 3 ≥ 5 / 9 * c + 4 / 9 := by 
    apply my_ineq c hc 
  linarith