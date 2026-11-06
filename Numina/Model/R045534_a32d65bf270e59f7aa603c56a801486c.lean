import Mathlib

open Real Set
open scoped BigOperators
/- (2) If the function $f(x)=\log _{a} x(a>0$, and $a \neq 1)$ satisfies $f\left(\frac{2}{a}\right)>f\left(\frac{3}{a}\right)$, then the solution set of $f\left(1-\frac{1}{x}\right)>1$ is ( ).
(A) $0<x<\frac{1}{a}$
(B) $0<x<\frac{1}{1-a}$
(C) $1<x<\frac{1}{a}$
(D) $1<x<\frac{1}{1-a}$ -/
set_option linter.unusedVariables false
theorem algebra_269752 {a x : ℝ} (h1 : 0 < a) (h2 : a ≠ 1) (h3 : 0 < x) (h4 : logb a (2 / a) > logb a (3 / a)) (h5 : 0 < 1 - 1/x) (h6 : 1 < logb a (1 - 1/x)): 1 < x ∧ x < 1 / (1 - a) := by 
  have h7 : logb a (2 / a) = logb a 2 - logb a a := by 
    rw [logb_div (by positivity) (by positivity)]
  have h8 : logb a (3 / a) = logb a 3 - logb a a := by
    rw [logb_div (by positivity) (by positivity)]
  have h8' : logb a 2 > logb a 3 := by 
    have eq1 : logb a (2 / a) = logb a 2 - logb a a := h7
    have eq2 : logb a (3 / a) = logb a 3 - logb a a := h8
    have h9 : logb a 2 - logb a a > logb a 3 - logb a a := by 
      linarith [h4, eq1, eq2]
    linarith 
  have ha1 : a < 1 := by 
    by_contra h 
    push_neg at h 
    have h9 : a ≥ 1 := by linarith 
    by_cases h11 : a > 1 
    · -- logb a is strictly increasing.
      -- `logb a 2 > logb a 3` would require `2 > 3` which is false.
      -- This is a contradiction.
      have h10 : logb a 2 ≤ logb a 3 := by 
        apply Real.logb_le_logb_of_le 
        all_goals 
        try linarith 
      linarith 
    · -- We know from h9: a ≥ 1 and h11: ¬ (a > 1)
      -- This forces a = 1. But h2 says a ≠ 1. This is a contradiction.
      -- Let's establish this contradiction. If a = 1, it's invalid.
      have h12 : a = 1 := by 
        linarith 
      tauto 
  -- Prove 1 < x 
  have h9 : 1 < x := by
    have h10 : 0 < 1 - 1 / x := h5 
    have h11 : 1 / x < 1 := by 
      nlinarith 
    have h12 : 1 < x := by
      have h13 : x > 0 := by linarith 
      have h14 : 1 / x < 1 := h11 
      have : x > 1 := by
        by_contra h 
        push_neg at h 
        have h17 : x ≤ 1 := by linarith 
        have h18 : 1 / x ≥ 1 := by
          apply (le_div_iff₀ (by linarith)).mpr 
          nlinarith 
        nlinarith 
      linarith 
    linarith 
  -- Prove x < 1 / (1 - a) 
  have h8 : 1 - 1 / x < a := by 
    have h9 : 1 < logb a (1 - 1 / x) := h6 
    have ha14 : logb a a = 1 := by 
      rw [logb_eq_iff_rpow_eq] <;> (norm_num) <;> linarith 
    have h10 : 1 - 1 / x < a := by 
      by_contra h 
      push_neg at h 
      -- We want to show the contradiction that `1 - 1/x ≥ a` implies `logb a (1 - 1 / x) ≤ logb a a`.
      -- This would contradict with `1 < logb a (1 - 1 / x)`.
      have h14 : logb a (1 - 1 / x) ≤ logb a a := by 
        have h13 : 1 - 1 / x ≥ a := by linarith 
        have h14a : logb a (1 - 1 / x) = (log (1 - 1 / x)) / (log a) := by 
          field_simp [logb]
        have h14b : logb a a = (log a) / (log a) := by 
          field_simp [logb]
        rw [h14a, h14b]
        have h15 : log a < 0 := by 
          have : a < (1 : ℝ) := by linarith [ha1] 
          have h17 : log a < log (1 : ℝ) := by 
            apply Real.log_lt_log
            all_goals 
            linarith [h1, this]
          have h18 : log (1 : ℝ) = 0 := Real.log_one
          have : log a < (0 : ℝ) := by 
            linarith [h17, h18]
          linarith 
        have h16 : log (1 - 1 / x) ≥ log a := by 
          apply Real.log_le_log
          all_goals 
          try linarith [h5, h13, h1] 
        have h15' : (log (1 - 1 / x)) / (log a) ≤ (log a) / (log a) := by 
          have h16' : log (1 - 1 / x) ≥ log a := h16 
          have h15' : log a < 0 := h15 
          apply (div_le_div_right_of_neg (by linarith)).mpr 
          nlinarith 
        simpa using h15' 
      have h11' : logb a (1 - 1 / x) ≤ 1 := by 
        rw [show logb a a = 1 by linarith [ha14]] at h14 
        linarith 
      nlinarith 
    linarith 
  -- Prove x < 1 / (1 - a) 
  have h10 : x < 1 / (1 - a) := by 
    have h10 : 1 - 1 / x < a := h8 
    have h11 : 1 - a > 0 := by 
      linarith [show a < 1 by linarith] 
    have h14 : 1 / x > 1 - a := by 
      nlinarith 
    have h15 : x > 0 := by linarith 
    have h18 : 0 < (1 - a : ℝ) := by linarith 
    have h19 : 0 < x := by linarith 
    have : x < 1 / (1 - a) := by 
      have h20 : 1 / (1/x : ℝ) < 1 / (1 - a : ℝ) := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr 
        field_simp at h14 ⊢
        nlinarith 
      field_simp at h20 ⊢ 
      nlinarith 
    linarith 
  exact ⟨h9, h10⟩