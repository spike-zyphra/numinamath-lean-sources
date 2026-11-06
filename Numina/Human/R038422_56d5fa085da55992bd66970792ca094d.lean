import Mathlib

/- 265*. Prove that if $x_{1}$ and $x_{2}$ are the roots of the equation $x^{2}-6 x+1=0$, then $x_{1}^{n}+x_{2}^{n}$ for any integer $n$ is an integer not divisible by 5. -/
theorem algebra_130071 (x1 x2 : ℝ) (hx1 : x1^2 - 6 * x1 + 1 = 0) (hx2 : x2^2 - 6 * x2 + 1 = 0)
    (hx12 : x1 ≠ x2) (n : ℕ) :
    ∃ m : ℤ, x1^n + x2^n = m ∧ ¬5 ∣ m := by
  -- prove sum of roots is 6
  have h_sum : x1 + x2 = 6 := by
    have : (x1 + x2 - 6) * (x1 - x2) = 0 := by linear_combination hx1 - hx2
    rw [← sub_ne_zero] at hx12
    simp [hx12] at this
    linarith
  -- prove product of roots is 1
  have h_prod : x1 * x2 = 1 := by
    rw [← h_sum] at hx1
    linarith
  -- write x1^(n+2) + x2^(n+2) in terms of powers n and n+1
  have h (n : ℕ) : x1^(n+2) + x2^(n+2) = 6 * (x1^(n+1) + x2^(n+1)) - (x1^n + x2^n) := by
    rw [show (x1^n + x2^n) = 1 * (x1^n + x2^n) by ring]
    rw [← h_sum, ← h_prod]
    ring
  -- now use strong induction
  induction' n using Nat.strong_induction_on with k hk
  match k with
  -- manually prove for 0, 1, 2
  | 0 =>
    use 2
    simp; norm_num
  | 1 =>
    use 6
    simp [h_sum]; norm_num
  | 2 =>
    rw [h]
    simp [h_sum]
    use 34
    norm_num
  -- for k + 3, first extract the fact for k, k+1, k+2
  | k + 3 =>
    obtain ⟨m, hm1, hm2⟩ := hk (k+1) (by linarith)
    obtain ⟨m', hm1', hm2'⟩ := hk (k+2) (by linarith)
    obtain ⟨m'', hm1'', hm2''⟩ := hk (k) (by linarith)
    -- use 6 * m' - m as the intger value for k + 3
    use 6 * m' - m
    and_intros
    . rw [h, hm1, hm1']
      norm_cast
    -- to prove not divisble by 5, write 6 * m' - m as 35 * m - 6 * m'', and 6 * m'' is not divisible by 5
    . specialize h k
      rw [hm1, hm1', hm1''] at h
      norm_cast at h
      rw [h]
      ring_nf
      rw [← Iff.symm (dvd_sub_right _)]
      . exact mt (IsCoprime.dvd_of_dvd_mul_right (show IsCoprime (5:ℤ) 6 by norm_num)) hm2''
      . use 7 * m; ring