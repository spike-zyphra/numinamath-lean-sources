import Mathlib

open Polynomial

theorem algebra_6754 {b c : ℝ} (p : ℝ[X]) (hp : p = X ^ 4 + C 6 * X ^ 3 + C b * X ^ 2 + C c * X + C 18)
    (h : (X ^ 2 + C 5 * X + C 6) ∣ p) : b / c = 2 / 3 := by 
        rcases h with ⟨q, hq⟩
        have eq1 : p.eval (-2) = 0 := by 
          rw [show p = (X ^ 2 + C 5 * X + C 6) * q by rw [hq]]
          norm_num [eval_mul, eval_add, eval_pow, eval_X, eval_C]
          <;> try tauto
        have eq2 : p.eval (-3) = 0 := by 
          rw [show p = (X ^ 2 + C 5 * X + C 6) * q by rw [hq]]
          norm_num [eval_mul, eval_add, eval_pow, eval_X, eval_C]
          <;> try tauto
        rw [hp] at eq1 eq2
        simp [eval_add, eval_pow, eval_X, eval_C, eval_mul] at eq1 eq2
        norm_num at eq1 eq2
        have h1 : 2 * b - c = 7 := by
          linarith
        have h2 : 3 * b - c = 21 := by
          linarith
        have hb : b = 14 := by 
          linarith [h1, h2]
        have hc : c = 21 := by 
          linarith [hb, h1]
        have hbc : b / c = 2 / 3 := by 
          rw [hb, hc]
          all_goals norm_num 
          <;> try tauto
        exact hbc