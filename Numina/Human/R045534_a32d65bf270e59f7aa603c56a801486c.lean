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
  -- Simplify h4 by log_division theorem
  rw [logb_div (by norm_num)] at h4
  rw [logb_div (by norm_num)] at h4
  simp at h4
  -- Show that log(a)<0
  rw [← log_div_log] at h4
  rw [← log_div_log] at h4
  rw [← sub_lt_zero] at h4
  rw [div_sub_div_same] at h4
  rw [← log_div] at h4
  rw [div_neg_iff] at h4
  rcases h4 with ⟨num_pos, loga_neg⟩ | ⟨num_neg, loga_pos⟩
  any_goals linarith
  -- Show that 0<a<1
  have a_lt_one : a < 1 := by
    rw [log_neg_iff] at loga_neg
    exact loga_neg
    exact h1
  -- Simplify h6 with 0<a<1
  rw [← log_div_log] at h6
  rw [one_lt_div_of_neg] at h6
  rw [log_lt_log_iff] at h6
  any_goals linarith
  -- Simplify and prove the solution
  rw [sub_pos] at h5
  rw [div_lt_one] at h5
  constructor
  exact h5
  rw [lt_one_div]
  rw [sub_lt_iff_lt_add]
  rw [add_comm]
  rw [← sub_lt_iff_lt_add]
  exact h6
  any_goals linarith
  -- Show another case's hypothesis is false
  rw [log_div] at num_neg
  rw [sub_neg] at num_neg
  rw [log_lt_log_iff] at num_neg
  any_goals linarith
