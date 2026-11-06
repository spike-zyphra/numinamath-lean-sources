import Mathlib

open Real

/- Oldjuk meg a


$$

\left(\sqrt{1+\sin ^{2} x}-\sin x\right)\left(\sqrt{1+\cos ^{2} x}-\cos x\right)=1

$$


egyenletet.

 -/
theorem algebra_218486 (x : ℝ) :
    (sqrt (1 + sin x ^ 2) - sin x) * (sqrt (1 + cos x ^ 2) - cos x) = 1 ↔
    ∃ k : ℤ, x = 3 * π / 4 + k * π := by
  constructor
  rotate_right
  -- let's first verify the solution
  · rintro ⟨k, hk⟩
    -- split by cases on whether k is even
    cases' Int.even_or_odd k with keven kodd
    · -- if k is even, k=2m
      obtain ⟨m, mdef⟩ := Even.exists_two_nsmul k keven
      rw [mdef] at hk
      -- now we can compute sin and cos
      have hsin: sin x = √2/2 := by
        rw [hk, show ((2 • m):ℤ) * π = m * (2*π) by simp; norm_cast; ring_nf, Real.sin_add_int_mul_two_pi, show 3 * π / 4= π - π/4 by ring_nf, Real.sin_pi_sub, Real.sin_pi_div_four]
      have hcos: cos x = -(√2/2) := by
        rw [hk, show ((2 • m):ℤ) * π = m * (2*π) by simp; norm_cast; ring_nf, Real.cos_add_int_mul_two_pi, show 3 * π / 4= π - π/4 by ring_nf, Real.cos_pi_sub, Real.cos_pi_div_four]
      rw [hsin, hcos, div_pow, neg_pow, div_pow, sq_sqrt];
      norm_num; ring_nf
      rw [sq_sqrt, inv_pow, sq_sqrt]; norm_num; norm_num; norm_num;norm_num
    -- same for the other side
    · obtain ⟨m, mdef⟩ := Odd.exists_bit1 kodd
      rw [mdef, show 3 * π / 4 + ↑(2 * m + 1) * π = 7*π/4 + 2*m*π by simp; ring_nf] at hk
      have hsin: sin x = -√2/2 := by
        rw [hk, show 2 * ↑m * π = m * (2*π) by ring_nf, Real.sin_add_int_mul_two_pi, show 7*π/4 = -(π/4) + 2*π by ring_nf, Real.sin_add_two_pi, Real.sin_neg, Real.sin_pi_div_four, neg_div]
      have hcos: cos x = √2/2 := by
        rw [hk, show 2 * ↑m * π = m * (2*π) by ring_nf, Real.cos_add_int_mul_two_pi, show 7*π/4 = -(π/4) + 2*π by ring_nf, Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_four,]
      rw [hsin, hcos, div_pow, neg_pow, neg_sq, div_pow, sq_sqrt (by norm_num)]; norm_num; field_simp; ring_nf
      rw [sq_sqrt (by norm_num), sq_sqrt (by norm_num)]; norm_num

  -- let's now solve the equation
  intro h
  apply congr_arg (fun t => t * (sqrt (1 + cos x ^ 2) + cos x)) at h
  rw [one_mul, mul_assoc, mul_comm (√(1 + cos x ^ 2) - cos x), ← sq_sub_sq, sq_sqrt (by nlinarith), add_sub_assoc, sub_self, add_zero, mul_one] at h
  -- we can pull sqrts to one side to prepare to square and eliminate them
  have h2: √(1+sin x^2) - √(1+cos x^2) = sin x + cos x := by linarith
  apply congr_arg (fun t => t^2) at h2
  conv_lhs at h2 =>
    calc _
    _ = √(1 + sin x ^ 2)^2 - 2 * √(1 + sin x ^ 2) * √(1 + cos x ^ 2) + √(1 + cos x ^ 2) ^ 2 := by ring_nf
    _ = (1 + sin x ^ 2) - 2 * √((1 + sin x ^ 2) * (1 + cos x ^ 2)) + (1 + cos x ^ 2) := by rw[sq_sqrt (by nlinarith), sq_sqrt (by nlinarith), sqrt_mul (by nlinarith)]; ring_nf
    _ = 2 + (sin x ^2 + cos x ^2) - 2 * √(1 + (sin x ^ 2 + cos x ^ 2) + sin x ^ 2 * cos x ^ 2) := by ring_nf
    _ = 3 - 2 * √(2 + sin x ^ 2 * cos x ^ 2) := by rw [sin_sq_add_cos_sq]; ring_nf
  rw [show (sin x + cos x) ^ 2 = 1 + 2 * sin x * cos x by ring_nf; rw [add_assoc, sin_sq_add_cos_sq]; ring_nf] at h2
  -- another removal of sqrts
  have h3:√(2+sin x^2*cos x^2) = 1 - sin x * cos x := by linarith
  apply congr_arg (fun t => t^2) at h3
  rw [sq_sqrt (by nlinarith)] at h3; ring_nf at h3; simp at h3
  -- double angle
  rw [show sin x * cos x * 2 = 2 * sin x * cos x by ring_nf, ← Real.sin_two_mul] at h3
  -- therefore sin 2x = -1
  have h4: sin (2*x) = -1 := by linarith
  apply Real.sin_eq_neg_one_iff.mp at h4
  obtain ⟨k, hk⟩ := h4
  -- easy finish
  apply congr_arg (fun t => t / 2) at hk
  ring_nf at hk;
  use (k-1)
  rw [← hk, show π * (-1 / 4) + π * ↑k  = π*(k-1/4) by ring_nf, show 3 * π / 4 + ↑(k - 1) * π = π*(3/4 + (-1+k)) by ring_nf; rw [Int.cast_add]; simp; ring_nf]; ring_nf