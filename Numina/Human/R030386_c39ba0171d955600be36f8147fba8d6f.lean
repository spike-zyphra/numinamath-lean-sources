import Mathlib

open Real Set
open scoped BigOperators

/- Example 18. Solve the inequality


$$

5^{\frac{1}{4} \log _{5}^{2} x} \geqslant 5 x^{\frac{1}{5} \log _{5} x}

$$
 -/
theorem inequalities_254301 {x : ℝ} (hx : 0 < x) :
    5 ^ ((1 / 4) * logb 5 x ^ 2) ≥ 5 * x ^ ((1 / 5) * logb 5 x) ↔
    x ∈ Ioc 0 (5 ^ (-2 * sqrt 5)) ∪ Ici (5 ^ (2 * sqrt 5)) := by
  simp
  constructor
  · intro h
    -- let's take the log of both sides
    have h':= (Real.logb_le_logb (b:=5) (by norm_num) (by simp; apply Real.rpow_pos_of_pos hx) (by apply Real.rpow_pos_of_pos (by norm_num))).mpr h
    -- and simplify
    rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_mul (by norm_num) (by apply ne_of_gt; apply Real.rpow_pos_of_pos hx), Real.logb_rpow_eq_mul_logb_of_pos hx] at h'
    norm_num at h'; ring_nf at h'
    -- simplify at h' to expose logb
    have h'' : 20 ≤ logb 5 x ^ 2 := by linarith
    -- sqrt both sides
    have h''' : √20 ≤ |logb 5 x| := by
      refine (sqrt_le_left ?_).mpr ?_
      simp
      simp; assumption
    -- now we have an inequality on absolute value which splits by cases
    have h2:= le_abs'.mp h'''
    cases' h2 with h2 h2
    · apply (Real.logb_le_iff_le_rpow (by norm_num) hx).mp at h2
      left
      constructor;
      exact hx
      suffices √20 = 2 * √5 by
        rw [this] at h2; assumption
      rw [show (20:ℝ)=2^2*5 by norm_num, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
    · apply (Real.le_logb_iff_rpow_le (by norm_num) hx).mp at h2
      right
      suffices √20 = 2 * √5 by
        rw [this] at h2; assumption
      rw [show (20:ℝ)=2^2*5 by norm_num, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
  -- now we need to prove the other direction, mostly repeating the steps
  · intro h
    apply (Real.logb_le_logb (b:=5) (by norm_num) (by simp; apply Real.rpow_pos_of_pos hx) (by apply Real.rpow_pos_of_pos (by norm_num))).mp
    rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_mul (by norm_num) (by apply ne_of_gt; apply Real.rpow_pos_of_pos hx), Real.logb_rpow_eq_mul_logb_of_pos hx]
    norm_num; ring_nf
    suffices 20 ≤ logb 5 x ^ 2 by linarith
    suffices √20 ≤ |logb 5 x| by
      rw [← Real.sqrt_sq_eq_abs] at this
      refine (sqrt_le_sqrt_iff' ?_).mp this
      norm_num
    apply le_abs'.mpr
    cases' h with h h
    · have h:=h.right
      left
      apply (Real.logb_le_iff_le_rpow (by norm_num) hx).mpr
      suffices √20 = 2 * √5 by
        rw [this]; assumption
      rw [show (20:ℝ)=2^2*5 by norm_num, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
    · right
      apply (Real.le_logb_iff_rpow_le (by norm_num) hx).mpr
      suffices √20 = 2 * √5 by
        rw [this]; assumption
      rw [show (20:ℝ)=2^2*5 by norm_num, sqrt_mul (by norm_num), sqrt_sq (by norm_num)]