import Mathlib

/- 6.22 Given $x=\frac{1}{2}\left(1991^{\frac{1}{n}}-1991^{-\frac{1}{n}}\right)$ ( $n$ is a natural number). Then the value of $\left(x-\sqrt{1+x^{2}}\right)^{n}$ is
(A) $1991^{-1}$.
(B) $-1991^{-1}$.
(C) $(-1)^{n} 1991$.
(D) $(-1)^{n} 1991^{-1}$.
(China Junior High School Mathematics Competition, 1991) -/
theorem algebra_215890 {n : ℕ} (hn : n ≠ 0) (x : ℝ)
    (hx : x = (1991 ^ ((1 : ℝ) / n) - 1991 ^ (-(1 : ℝ) / n)) / 2) :
    (x - Real.sqrt (1 + x ^ 2)) ^ n = (-1) ^ n / 1991 := by
    -- first prove 1+x^2 = [(1991^(1/n) + 1991^(-1/n))/2]^2 by algebraic manipulation
    have hx' :  1 + x^2 = ((1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2)^2 := by calc
      1 + x^2 = 1 + ((1991 ^ ((1 : ℝ) / n) - 1991 ^ (-(1 : ℝ) / n)) / 2)^2 := by rw [hx]
      _ = 1 + ((1991^((2:ℝ)/n) - 2 +  1991^(-(2:ℝ)/n))/4) := by
        congr
        ring_nf
        simp [Nat.ofNat_nonneg, ← Real.rpow_add, Real.rpow_mul]
        rw [neg_mul_eq_neg_mul, Real.rpow_mul]
        norm_cast
        simp
      _ =  ((1991 ^ ((1 : ℝ) / n) + 1991 ^ (-(1 : ℝ) / n)) / 2)^2 := by
        ring_nf
        simp [Nat.ofNat_nonneg, ← Real.rpow_add, Real.rpow_mul]
        rw [neg_mul_eq_neg_mul, Real.rpow_mul]
        norm_cast
        simp
    -- now plugging in values, do some algebraic manipulation to figure out the result.
    rw [hx', hx]
    rw [Real.sqrt_sq]
    . ring_nf
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      . field_simp
        ring
      . positivity
    . positivity