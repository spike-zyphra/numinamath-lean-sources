import Mathlib

open Real

/- 2. Given the sum $S=\cos \frac{n \pi}{7}+\cos \frac{3 n \pi}{7}+\cos \frac{5 n \pi}{7}, n \in \mathbb{N}$. If $n$ is not divisible by 7, then
$$
S=-\frac{1}{2} \cos n \pi=\left\{\begin{array}{rc}
\frac{1}{2}, & \text { for } n \text { odd } \\
-\frac{1}{2}, & \text { for } n \text { even }
\end{array} .\right.
$$
Prove! What is $S$ if $n$ is divisible by 7? -/
theorem algebra_251827 {n : ℤ} (hn : n % 7 ≠ 0) :
    cos (n * π / 7) + cos (3 * n * π / 7) + cos (5 * n * π / 7) =
    if Even n then -1 / 2 else 1 / 2 := by
  -- Let s = sin(n * π / 7).
  set s := sin (n * π / 7)
  -- Show that s ≠ 0.
  have hs0 : s ≠ 0 := by
    -- Assume that s = 0 and show that n % 7 = 0.
    contrapose! hn
    -- s = 0 implies that n * π / 7 = k * π for some k ∈ ℤ.
    rw [sin_eq_zero_iff] at hn
    have ⟨k, hk⟩ := hn
    -- It is enough to show that n = 7 * k.
    suffices n = 7 * k by simp [this]
    rify
    -- Multiply n = 7 * k by π / 7 and get the result from hk.
    rw [← mul_left_inj' (show π / 7 ≠ 0 by positivity)]
    linear_combination -hk
  -- Multiply the equality by 2 * s ≠ 0.
  rw [← mul_right_inj' (show 2 * s ≠ 0 by positivity)]
  calc
    -- We have
    -- 2 * s * cos (n * π / 7) = sin (2 * (n * π / 7)),
    -- 2 * s * cos (3 * n * π / 7) = sin (6 * n * π / 7) - sin (4 * n * π / 7), and
    -- 2 * s * cos (5 * n * π / 7) = sin (4 * n * π / 7) - sin (2 * n * π / 7).
    _ = sin (2 * (n * π / 7)) + (sin (6 * n * π / 7) - sin (4 * n * π / 7)) + (sin (4 * n * π / 7) - sin (2 * n * π / 7)) := by
      rw [mul_add, mul_add (2 * s)]
      rw [← sin_two_mul, two_mul_sin_mul_cos, two_mul_sin_mul_cos]
      ring_nf
      rw [show n * π * (-2 / 7) = -(n * π * (2 / 7)) by ring, show n * π * (-4 / 7) = -(n * π * (4 / 7)) by ring]
      simp_rw [sin_neg]
      ring
    -- Simplify the expression and get sin (6 * n * π / 7) = sin (n * π - n * π / 7).
    _ = sin (n * π - n * π / 7) := by ring_nf
    -- We have sin (n * π - n * π / 7) = 2 * s * (-1 / 2 * cos (n * π)).
    _ = 2 * s * (-1 / 2 * cos (n * π)) := by
      rw [sin_sub, sin_int_mul_pi]
      ring
    -- It is left to show that cos (n * π) = -1 when n is even and cos (n * π) = 1 when n is odd.
    _ = 2 * s * if Even n then -1 / 2 else 1 / 2 := by
      congr
      rw [show n * π = 0 + n * π by ring, cos_add_int_mul_pi, cos_zero]
      split_ifs with hn
      · rw [hn.neg_one_zpow]
        norm_num
      · simp at hn
        rw [hn.neg_one_zpow]
        norm_num

-- Show that n % 7 = 0 implies that the sum is equal to 3 when n is even and to -3 when n is odd.
theorem algebra_251827_part2 {n : ℤ} (hn : n % 7 = 0) :
    cos (n * π / 7) + cos (3 * n * π / 7) + cos (5 * n * π / 7) =
    if Even n then 3 else -3 := by
  -- n % 7 = 0 implies that n = 7 * k for some k ∈ ℤ.
  have ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hn
  subst n
  push_cast
  ring_nf
  nth_rw 1 [show k * π = 0 + k * π by ring]
  rw [show k * π * 3 = (0 + k * π) + k * (2 * π) by ring]
  rw [show k * π * 5 = (0 + k * π) + (2 * k : ℤ) * (2 * π) by simp; ring]
  -- Simplify the expression and get 3 * (-1)^k.
  simp_rw [cos_add_int_mul_two_pi, cos_add_int_mul_pi, cos_zero]
  -- If n is even then k is also even, if n is odd then k is also odd.
  simp [Int.even_mul, show ¬ Even (7 : ℤ) by decide]
  split_ifs with hk
  · rw [hk.neg_one_zpow]
    norm_num
  · simp at hk
    rw [hk.neg_one_zpow]
    norm_num