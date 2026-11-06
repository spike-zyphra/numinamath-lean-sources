import Mathlib

/- $1 \cdot 65 a, b$ and $n$ are fixed natural numbers, and for any natural number $k(k \neq b), a-$ $k^{n}$ is divisible by $b-k$. Prove that $a=b^{n}$.
(4th All-Russian Mathematical Olympiad, 1964) -/
theorem number_theory_241756 (a b n: ℕ) (h : ∀ k ≠ b, (b - k : ℤ) ∣  a - k^n) :
    a = b^n := by
  -- first we'll prove for all k ≠ b, k - b ∣ a - b^n
  replace h : ∀ k ≠ b, (k - b : ℤ) ∣ a - b ^ n := by
    rintro k hkb
    replace h := Int.neg_dvd.mpr <| h k hkb
    rw [show -(b - k) = (k - b : ℤ) by ring] at h
    -- mainly utilize k - b ∣ k^n - b^n and add the two divisibilities
    have h' : (k - b : ℤ) ∣ k^n - b^n := by exact sub_dvd_pow_sub_pow (k : ℤ) b n
    convert Int.dvd_add h h' using 1
    ring
  -- we'll prove the integer versions and prove a - b^n = 0
  zify
  have : (a - b^n : ℤ) = 0 := by
    -- use h on |a-b^n| + 1 + b, this'll ensure a divisor larger than a-b^n
    replace h : ↑((a-b^n : ℤ).natAbs +1+b) - (b: ℤ) ∣ a - b^n := by
      apply h ((a-b^n : ℤ).natAbs +1+b)
      omega
    push_cast at h
    conv_lhs at h => ring_nf
    -- change rhs of division to |a-b^n|, then divisor is larget then it and it is also positive, hence it is 0
    replace h := dvd_abs _ _ |>.mpr h
    suffices |(a-b^n : ℤ)| = 0 by
      exact abs_eq_zero.mp this
    refine Int.eq_zero_of_dvd_of_nonneg_of_lt ?_ ?_ h
    . positivity
    . linarith
  linarith