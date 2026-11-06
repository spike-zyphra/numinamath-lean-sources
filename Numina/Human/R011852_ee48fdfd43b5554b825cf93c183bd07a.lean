import Mathlib

open Real Set
open scoped BigOperators

/- 9.195. $\log _{3} \log _{x^{2}} \log _{x^{2}} x^{4}>0$. -/
theorem algebra_171194 {x : ℝ} (logValid: 0 < logb (x^2) (logb (x^2) (x^4))) (log2Valid: 0 < logb (x^2) (x^4)) (log3Valid: 0 < x^4):
    logb 3 (logb (x^2) (logb (x^2) (x^4))) > 0 ↔
    x ∈ Ioo (-sqrt 2) (-1) ∪ Ioo 1 (sqrt 2) := by
  -- log3Valid can be simplified
  have hxzero: x ≠0 := by
    by_contra h; rw [h] at log3Valid; linarith
  -- we first get rid of the inner log
  rw [show x^4 = (x^2)^2 by ring_nf, Real.logb_pow, Real.logb_self_eq_one_iff.mpr (by
    constructor
    simp; assumption
    constructor
    intro h
    rw [h, Real.logb_one_left] at logValid
    linarith
    intro h
    rw [h, Real.logb_neg_eq_logb, Real.logb_one, mul_zero, Real.logb_zero] at logValid
    linarith
  )] at logValid
  rw [show x^4 = (x^2)^2 by ring_nf, Real.logb_pow]
  norm_num at *
  -- we keep unfolding the logs
  constructor
  · intro h
    simp at h
    -- we need to compare x^2 with 1 to be able to use log rules
    cases' lt_trichotomy (x^2) 1 with hl hr
    · -- this is impossible
      apply (Real.logb_pos_iff_of_base_lt_one (by nlinarith [sq_nonneg x]) hl (by norm_num)).mp at logValid
      linarith
    cases' hr with hl hr
    · --also not possible
      rw [hl, Real.logb_one_left] at logValid
      linarith
    · -- this can be handled
      rw [Real.logb_self_eq_one hr, mul_one] at h
      apply (Real.logb_pos_iff (by norm_num) logValid).mp at h
      apply (lt_logb_iff_rpow_lt hr (by norm_num)).mp at h
      simp at h
      -- just basic methods from here
      cases' lt_trichotomy x 0 with hn hzp
      left
      constructor
      exact neg_sqrt_lt_of_sq_lt h
      nlinarith
      cases' hzp with hz hp
      exfalso; trivial
      right; constructor
      nlinarith
      exact lt_sqrt_of_sq_lt h
  -- other side just needs checking, mostly similar steps
  · intro h
    cases' h with h h
    · refine (logb_pos_iff ?_ ?_).mpr ?_
      norm_num
      refine (logb_pos_iff ?_ ?_).mpr ?_
      nlinarith
      apply mul_pos; norm_num
      refine (logb_pos_iff ?_ ?_).mpr ?_
      nlinarith
      nlinarith
      simp
      rw [abs_of_neg (by linarith)]; linarith
      rw [Real.logb_self_eq_one (by nlinarith)]; norm_num
      rw [Real.logb_self_eq_one (by nlinarith)]; norm_num;
      refine (lt_logb_iff_rpow_lt ?_ ?_).mpr ?_
      nlinarith
      norm_num
      simp
      refine sq_lt.mpr ?_
      constructor
      linarith
      linarith
    · refine (logb_pos_iff ?_ ?_).mpr ?_
      norm_num
      refine (logb_pos_iff ?_ ?_).mpr ?_
      nlinarith
      apply mul_pos; norm_num
      refine (logb_pos_iff ?_ ?_).mpr ?_
      nlinarith
      nlinarith
      refine lt_sq_of_sqrt_lt ?_
      simp; linarith
      rw [Real.logb_self_eq_one (by nlinarith)]; norm_num
      rw [Real.logb_self_eq_one (by nlinarith)]; norm_num;
      refine (lt_logb_iff_rpow_lt ?_ ?_).mpr ?_
      nlinarith
      norm_num
      simp
      refine sq_lt.mpr ?_
      constructor
      linarith
      linarith