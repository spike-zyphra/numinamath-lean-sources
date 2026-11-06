import Mathlib

open Real

/-Solve for $x$: $4x^{1/3}-2 \cdot \frac{x}{x^{2/3}}=7+\sqrt[3]{x}$.-/
theorem algebra_14631 {x : ℂ} :
4 * x ^ ((1 : ℂ) / 3) - 2 * x / x ^ ((2 : ℂ) / 3) = 7 + x ^ ((1 : ℂ) / 3) ↔
x = 343 := by
-- Break "iff"
  constructor
-- Use straightfoward simplification to solve for $x$
  · intro h
    have xne0 : x ≠ 0 := by intro; simp_all
    nth_rw 2 [show x=x^(1:ℂ) by simp] at h
    rw [mul_div_assoc, ← Complex.cpow_sub] at h
    norm_num at h
    apply_fun (fun t => t - x ^ ((1:ℂ)/3)) at h; ring_nf at h
    apply_fun (fun t => t * t * t) at h
    repeat rw [← Complex.cpow_add] at h
    norm_num at h; any_goals assumption
-- Conversely, check that $x=343$ satisfies the equation
  intro hx; nth_rw 2 [show x=x^(1:ℂ) by simp]
  rw [mul_div_assoc, ← Complex.cpow_sub]; norm_num; ring_nf
  have : x ^ ((1:ℂ)/3) = 7 := by
    rw [hx, show (343:ℂ)=7^(3:ℂ) by norm_num]
    rw [← Complex.cpow_mul]; norm_num
    simp; rw [show (7:ℂ)=(7:ℝ) by rfl, Complex.log_im]
    rw [Complex.arg_ofReal_of_nonneg]
    norm_num; exact pi_pos; norm_num
    simp; rw [show (7:ℂ)=(7:ℝ) by rfl, Complex.log_im]
    rw [Complex.arg_ofReal_of_nonneg]
    norm_num; exact pi_nonneg; norm_num
  rw [this]; norm_num; rw [hx]; norm_num