import Mathlib

open Complex

theorem algebra_311821 {z : ℂ} (hz : 11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 = 0) :
    z.abs = 1 := by
  have : 0 < (11 * z.re) ^ 2 + (11 * z.im + 10) ^ 2 := by
    by_contra! h'; have : 0 ≤ (11 * z.re) ^ 2 := by apply sq_nonneg
    have : 0 ≤ (11 * z.im + 10) ^ 2 := by apply sq_nonneg
    replace this : (11 * z.im + 10) ^ 2 = 0 := by linarith
    replace h' : (11 * z.re) ^ 2 = 0 := by linarith
    simp at this h'; replace this : z.im = -10/11 := by linarith
    rw [← re_add_im z, h', this] at hz; push_cast at hz
    norm_num at hz; ring_nf at hz; rw [I_sq] at hz
    norm_num at hz
  rw [sub_eq_zero, ← eq_sub_iff_add_eq] at hz
  rw [show 11 * z ^ 10 + 10 * I * z ^ 9 = z ^ 9 * (11 * z + 10 * I) by ring] at hz
  rw [← eq_div_iff] at hz; let abseq := hz
  apply_fun fun t => ‖t‖ at abseq
  rw [norm_pow, norm_div] at abseq
  repeat rw [norm_eq_abs] at abseq
  repeat rw [abs_eq_sqrt_sq_add_sq] at abseq
  simp at abseq; rw [← Real.sqrt_div] at abseq; symm at abseq
  rw [Real.sqrt_eq_iff_eq_sq, ← pow_mul, show 9*2 = 2*9 by ring] at abseq
  rw [pow_mul, Real.sq_sqrt] at abseq
  by_contra!; rw [abs_eq_sqrt_sq_add_sq, ne_iff_lt_or_gt] at this
  rcases this with h|h
  · rw [Real.sqrt_lt] at h; norm_num at h
    replace abseq : ((11 + 10 * z.im) ^ 2 + (10 * z.re) ^ 2) / ((11 * z.re) ^ 2 +
    (11 * z.im + 10) ^ 2) < 1 := by
      rw [abseq, show (1:ℝ) = 1^9 by simp]; gcongr
    rw [div_lt_iff₀, one_mul, ← sub_pos] at abseq
    ring_nf at abseq; linarith
    all_goals positivity
  rw [gt_iff_lt, Real.lt_sqrt] at h; norm_num at h
  replace abseq : 1 < ((11 + 10 * z.im) ^ 2 + (10 * z.re) ^ 2) / ((11 * z.re) ^ 2 +
    (11 * z.im + 10) ^ 2) := by
      rw [abseq, show (1:ℝ) = 1^9 by simp]; gcongr
  rw [lt_div_iff₀, one_mul, ← sub_pos] at abseq
  ring_nf at abseq; linarith
  any_goals positivity
  intro h; apply_fun fun t => t.abs at h
  simp [abs_eq_sqrt_sq_add_sq] at h
  rw [Real.sqrt_eq_zero] at h; linarith
  positivity
