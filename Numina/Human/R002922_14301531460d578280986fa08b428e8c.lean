import Mathlib

open Real

/- 6. If $a>0, b>0$, and $\arcsin a+\arcsin b=\frac{\pi}{2}, m=\log _{2} \frac{1}{a}+\log _{2} \frac{1}{b}$, then the range of $m$ is $\qquad$ . -/

theorem algebra_130548 (a b : ℝ) (ha1 : 0 < a) (ha2: a ≤ 1) (hb1 : 0 < b) (hb2: b ≤ 1) (h : arcsin a + arcsin b = π/2) :
  1 ≤ logb 2 (1/a) + logb 2 (1/b)
  := by

    -- Prove some trivial auxiliary lemmas
    have aux3 : arcsin b = π/2 - arcsin a := by
      linarith [h]
    have aux4 : 0 ≤ 1 - a^2 := by
      apply sub_nonneg_of_le
      rw [sq_le_one_iff₀ (le_of_lt ha1)]
      exact ha2

    --Prove main relation between a b
    have hyp: a^2 + b^2 = 1 := by
      calc
        a^2 + b^2 = (sin (arcsin a)) ^2 + (sin (arcsin b)) ^2 := by
          rw [sin_arcsin (by linarith [ha1]) (by linarith [ha2]), sin_arcsin (by linarith [ha2]) hb2]
        _ = (sin (arcsin a))^2 + (sin (π/2 - arcsin a)) ^2 := by
          simp [aux3]
        _ = (sin (arcsin a))^2 + (cos (arcsin a))^2 := by
          rw [sin_pi_div_two_sub]
        _ = (sin (arcsin a))^2 + (√(1 -  a^2))^2 := by
          rw [<- cos_arcsin]
        _ = a^2 + (1 - a^2) := by
          rw [sin_arcsin (by linarith [ha1]) ha2]
          rw [sq_sqrt aux4]
        _ = 1 := by
          ring
    -- Prove more auxiliary lemmas
    have aux5 : 0 ≤ a^2  - 2*a*b + b^2 := by
      rw [<- sub_sq]
      exact sq_nonneg (a - b)
    have hyp2 : a*b ≤ 1/2 := by
      linarith [hyp, aux5]

    -- Conclude inequality
    have hyp3 : logb 2 (1/a) + logb 2 (1/b) ≥ 1 := by
      calc
        logb 2 (1/a) + logb 2 (1/b) = logb 2 (1/(a*b)) := by
          rw [<- logb_mul]
          rw [one_div_mul_one_div]
          . rw [one_div]
            apply inv_ne_zero
            apply ne_iff_lt_or_gt.mpr
            right
            rw [gt_iff_lt]
            exact ha1
          . rw [one_div]
            apply inv_ne_zero
            apply ne_iff_lt_or_gt.mpr
            right
            rw [gt_iff_lt]
            exact hb1

        _ ≥ logb 2 (2) := by
          rw [ge_iff_le]
          apply logb_le_logb_of_le
          . linarith
          . linarith
          . rw [one_div]
            have hab_pos : 0 < a * b := by
              exact mul_pos ha1 hb1
            have trivial : (0 : ℝ) < 2 := by
              linarith
            rw [le_inv_comm₀ trivial hab_pos]
            rw [<- one_div]
            exact hyp2
        _ = 1 := by
          apply Real.logb_self_eq_one
          norm_num
    rw [ge_iff_le] at hyp3
    exact hyp3