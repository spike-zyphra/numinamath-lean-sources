import Mathlib

set_option maxHeartbeats 0

/- Let $a,$ $b,$ $c,$ $d$ be positive real numbers.  Find the minimum value of
\[(1 + a)(1 + b)(1 + c)(1 + d) \left( \frac{1}{a} + \frac{1}{b} + \frac{1}{c} + \frac{1}{d} \right).\]
-/
theorem algebra_18850 :
    IsLeast { x : ℝ | ∃ a b c d : ℝ , 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ (1 + a) * (1 + b) * (1 + c) * (1 + d) * (1 / a + 1 / b + 1 / c + 1 / d) = x } (1024 / 27) := by
  unfold IsLeast
  constructor
  . {
    -- show that the value is achieved
    simp
    repeat use 1 / 3; simp
    ring_nf
  }
  . {
    -- show that the value is a lower bound
    unfold lowerBounds
    simp
    intros x a a_pos b b_pos c c_pos d d_pos h

    have weight_pos : 0 ≤ 1 / (4:ℝ)  := by norm_num
    -- the first time to use AM-GM, calculate the min of (1 + a), (1 + b), (1 + c), (1 + d)
    have mean1 {x:ℝ} (h: 0 < x): 4 * (x / 27) ^ (1 / 4:ℝ ) ≤ 1 + x := by
      have h1 := Real.geom_mean_le_arith_mean4_weighted
        weight_pos weight_pos weight_pos weight_pos
        (le_of_lt h) (show 0 ≤ 1 / 3 by norm_num) (show 0 ≤ 1 / 3 by norm_num) (show 0 ≤ 1 / 3 by norm_num)
        (by norm_num)
      rw [<-left_distrib, <-left_distrib, <-left_distrib] at h1
      ring_nf at h1
      rw [<-Real.rpow_natCast] at h1
      rw [<-Real.rpow_mul (show 0 ≤ 1 / 3 by norm_num)] at h1
      nth_rw 2 [mul_comm] at h1
      rw [Real.rpow_mul (show 0 ≤ 1 / 3 by norm_num)] at h1
      rw [Real.rpow_natCast] at h1
      ring_nf at h1
      rw [
        Real.rpow_def_of_pos h,
        Real.rpow_def_of_pos (by norm_num),
        <-Real.exp_add,
        <-right_distrib,
        <-Real.log_mul (by linarith) (by norm_num),
        <-Real.rpow_def_of_pos (by linarith),
        mul_one_div,
      ] at h1
      linarith
    have mean1_left_nonneg {x:ℝ} (h: 0 < x) : 0 < 4 * (x / 27) ^ (1 / 4:ℝ) := by
      have h : (x / 27) ^ (1 / 4:ℝ) > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      linarith
    -- the second time to use AM-GM, calculate the min of 1/a + 1/b + 1/c + 1/d
    have mean2 : 4 * (a⁻¹ ^ (1 / 4:ℝ) * b⁻¹ ^ (1 / 4:ℝ) * c⁻¹ ^ (1 / 4:ℝ) * d⁻¹ ^ (1 / 4:ℝ)) ≤ 1 / a + 1 / b + 1 / c + 1 / d := by
      have h1 := Real.geom_mean_le_arith_mean4_weighted
        weight_pos weight_pos weight_pos weight_pos
        (le_of_lt <| one_div_pos.mpr a_pos) (le_of_lt <| one_div_pos.mpr b_pos) (le_of_lt <| one_div_pos.mpr c_pos) (le_of_lt <| one_div_pos.mpr d_pos)
        (by norm_num)
      ring_nf at h1
      rw [<-right_distrib, <-right_distrib, <-right_distrib] at h1
      ring_nf
      linarith
    have mean2_left_pos : 0 < 4 * (a⁻¹ ^ (1 / 4:ℝ) * b⁻¹ ^ (1 / 4:ℝ) * c⁻¹ ^ (1 / 4:ℝ) * d⁻¹ ^ (1 / 4:ℝ)) := by
      have h: ∀a:ℝ, a > 0 → 0 < a⁻¹ ^ (1 / 4:ℝ) :=
        fun a => fun a_pos => Real.rpow_pos_of_pos (inv_pos_of_pos a_pos) (1 / 4)
      exact Right.mul_pos (show 0 < 4 by norm_num) (
        Right.mul_pos (Right.mul_pos (Right.mul_pos (h a a_pos) (h b b_pos)) (h c c_pos)) (h d d_pos))

    -- multiply the five inequalities
    have mul1 := mul_le_mul (mean1 a_pos) (mean1 b_pos) (le_of_lt <| mean1_left_nonneg b_pos) (by linarith)
    have mul1_left_pos := mul_pos (mean1_left_nonneg a_pos) (mean1_left_nonneg b_pos)
    have mul2 := mul_le_mul mul1 (mean1 c_pos) (le_of_lt <| mean1_left_nonneg c_pos) (by linarith)
    have mul2_left_pos := mul_pos mul1_left_pos (mean1_left_nonneg c_pos)
    have mul3 := mul_le_mul mul2 (mean1 d_pos) (le_of_lt <| mean1_left_nonneg d_pos) (by linarith)
    have mul3_left_pos := mul_pos mul2_left_pos (mean1_left_nonneg d_pos)
    have mul4 := mul_le_mul mul3 mean2 (le_of_lt mean2_left_pos) (by linarith)
    -- simplify the inequality
    simp at mul4
    rw [h] at mul4
    ring_nf at mul4

    rw [
      Real.rpow_def_of_pos (show 0 < a * (1 / 27) by linarith),
      Real.rpow_def_of_pos (show 0 < b * (1 / 27) by linarith),
      Real.rpow_def_of_pos (show 0 < c * (1 / 27) by linarith),
      Real.rpow_def_of_pos (show 0 < d * (1 / 27) by linarith),
      Real.rpow_def_of_pos <| inv_pos_of_pos a_pos,
      Real.rpow_def_of_pos <| inv_pos_of_pos b_pos,
      Real.rpow_def_of_pos <| inv_pos_of_pos c_pos,
      Real.rpow_def_of_pos <| inv_pos_of_pos d_pos,
    ] at mul4
    repeat rw [<-Real.exp_add] at mul4
    repeat rw [<-right_distrib] at mul4
    repeat rw [Real.log_mul (by linarith) (by linarith)] at mul4
    simp at mul4
    ring_nf at mul4
    rw [
      <-Real.log_inv,
      Real.exp_log (by norm_num),
      inv_mul_eq_div
    ] at mul4
    exact mul4
  }
