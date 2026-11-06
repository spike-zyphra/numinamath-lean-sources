import Mathlib

open Real Set
open scoped Real

/- 8.176. $\sin ^{3} x(1+\operatorname{ctg} x)+\cos ^{3} x(1+\operatorname{tg} x)=2 \sqrt{\sin x \cos x}$. -/
theorem algebra_168119 (x : ℝ) (cot_def: sin x ≠ 0 ) (tan_def: cos x ≠ 0) (sqrt_def: 0 ≤ sin x * cos x):
  sin x ^ 3 * (1 + 1 / tan x) + cos x ^ 3 * (1 + tan x) =
  2 * sqrt (sin x * cos x) ↔ ∃ k : ℤ, x = (π / 4) * (8 * k + 1) := by
  constructor
  · intro h
    -- let's write the equation with sin and cos only
    rw [Real.tan_eq_sin_div_cos, ← div_mul, mul_comm (1/sin x), mul_div, mul_one] at h
    rw [show 1 = sin x / sin x by rw [div_self cot_def], ← add_div, mul_div, div_self cot_def, show 1=cos x / cos x by rw [div_self tan_def], ←add_div, mul_div] at h
    -- we can cancel
    rw [show sin x ^ 3=sin x^2 * sin x by ring, mul_assoc, mul_comm (sin x ), ← mul_div, ← mul_div, div_self cot_def, mul_one] at h
    rw [show cos x ^ 3=cos x^2 * cos x by ring, mul_assoc, mul_comm (cos x ), ← mul_div, ← mul_div, div_self tan_def, mul_one] at h
    -- sin^2+cos^2=1
    rw [add_comm (sin x), ← add_mul, Real.sin_sq_add_cos_sq, one_mul, add_comm] at h
    -- we can clearly see that sin x + cos x ≥ 0
    have h1: 0 ≤ sin x + cos x := by nlinarith [sqrt_nonneg (sin x*cos x)]
    -- since their product is ≥ 0, they are both ≥ 0
    have hsin: 0 ≤ sin x := by nlinarith
    have hcos: 0 ≤ cos x := by nlinarith
    -- now let's move everything to the left and complete the square
    apply congr_arg (fun t => t-2*√(sin x * cos x)) at h
    ring_nf at h
    rw [show sin x + (cos x - √(sin x * cos x) * 2) = (√(sin x) - √(cos x))^2 by ring_nf; rw [sq_sqrt (by linarith), sq_sqrt (by linarith), sqrt_mul (by linarith)]; ring_nf] at h
    simp at h
    apply congr_arg (fun t => t + √(cos x)) at h
    ring_nf at h; apply (sqrt_inj hsin hcos).mp at h
    -- we can subtract cos and use additive theorems
    apply congr_arg (fun t => t - cos x) at h
    ring_nf at h
    have :=
      calc sin x - cos x
      _ = sin (x-Real.pi/4)*√2 := by rw [Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four, sub_mul]; ring_nf; rw [sq_sqrt (by norm_num)]; ring_nf
    rw [this] at h
    simp at h
    apply Real.sin_eq_zero_iff.mp at h
    -- now we just need to combine our result with the answer knowing sin x ≥ 0
    obtain ⟨n, hn⟩ := h
    use n/2;
    apply congr_arg (fun t => t+π/4) at hn; ring_nf at hn; rw [← hn]
    rw [mul_div, mul_one, mul_add, mul_one]
    simp; ring_nf
    rw [Int.cast_div (by
      refine even_iff_two_dvd.mp ?_
      by_contra h
      simp at h; unfold Odd at h; obtain ⟨k, hk⟩ := h
      rw [hk] at hn; rw [← hn] at hsin; ring_nf at hsin; simp at hsin;
      rw [show (1 + k * 2) * π + π * 4⁻¹ = π/4 + π + k*(2*π) by ring_nf, Real.sin_add_int_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_four] at hsin
      simp at hsin
      suffices 0 < √2/2 by linarith
      simp
    )]; ring_nf; simp
  -- verifying the solution takes mostly the same steps
  intro h
  obtain ⟨k, hk⟩ := h
  rw [show π / 4 * (8 * ↑k + 1) = π/4 + k*(2*π) by ring_nf] at hk
  rw [hk, Real.tan_eq_sin_div_cos, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi, Real.sin_pi_div_four, Real.cos_pi_div_four]; ring_nf
  simp; ring_nf
  rw [show √4=√(2^2) by norm_num, show √2^3=√2^2*√2 by ring_nf, show √2^4=(√2^2)^2 by ring, Real.sqrt_sq (by norm_num), Real.sq_sqrt (by norm_num)]
  ring_nf; field_simp; ring_nf; rw [Real.sq_sqrt (by norm_num)]; norm_num