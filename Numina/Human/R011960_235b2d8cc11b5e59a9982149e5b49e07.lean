import Mathlib

/- 7. Given $a, b>0$, and $\frac{1}{a}+\frac{1}{b}=1$, prove: for every $n \in N,(a+$ $b)^{n}-a^{n}-b^{n} \geqslant 2^{2 n}-2^{n+1}$. -/
theorem inequalities_163495 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a + 1 / b = 1) (n : ℕ) :
    (a + b) ^ n - a ^ n - b ^ n ≥ 2 ^ (2 * n) - 2 ^ (n + 1) := by
  -- for n=0 it's easy
  by_cases hnz:n=0
  · rw [hnz]; simp; norm_num
  have hpos: 1≤n := by omega
  -- we go by induction from 1
  induction n, hpos using Nat.le_induction with
  | base => ring_nf; norm_num
  | succ n hpos' ih =>
    rw [show (a + b) ^ (n + 1) - a ^ (n + 1) - b ^ (n + 1) = (a+b)*((a+b)^n - a^n - b^n) + a^n*b+a*b^n by ring_nf]
    -- multiply h by ab and obtain a*b=a+b
    apply congr_arg (fun x => x * a * b) at h
    rw [add_mul, add_mul, div_mul, div_self (by linarith), div_one, one_mul, mul_comm, ← mul_assoc, mul_div, mul_one, div_self (by linarith), one_mul, add_comm] at h
    -- we can also show that a+b≥4 by AM-GM on two variables
    have h0: a+b≥4 := by nlinarith [sq_nonneg (a-b)]
    -- now we calculate
    calc (a + b) * ((a + b) ^ n - a ^ n - b ^ n) + a ^ n * b + a * b ^ n
    _ ≥ (a + b) * (2 ^ (2 * n) - 2 ^ (n + 1)) + a ^ n * b + a * b ^ n := by simp; gcongr (a+b)*?_; exact ih (by linarith)
    _ ≥ 4 * (2 ^ (2 * n) - 2 ^ (n + 1)) + a ^ n * b + a * b ^ n := by gcongr; simp; gcongr; norm_num; linarith
    -- AM-GM on last two terms
    _ ≥ 4 * (2 ^ (2 * n) - 2 ^ (n + 1)) + 2 * √ (a ^ n * b * a * b^n) := by
      suffices a ^ n * b + a * b ^ n ≥ 2 * √ (a ^ n * b * a * b^n) by linarith
      have q:= Real.geom_mean_le_arith_mean2_weighted (w₁:=1/2) (w₂:=1/2) (p₁:=a^n*b) (p₂:=a*b^n) (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
      apply (mul_le_mul_right (a:=2) (by positivity)).mpr at q
      simp
      rw [← mul_add, mul_comm (1/2), ← Real.mul_rpow, ← Real.sqrt_eq_rpow, mul_comm, mul_assoc _ (1/2), show (1:ℝ)/2*2=1 by norm_num, mul_one, ← mul_assoc] at q
      exact q; positivity; positivity
    -- now we just simplify using a+b≥4
    _ = 4 * (2 ^ (2 * n) - 2 ^ (n + 1)) + 2 * √((a*b)^(n+1)) := by ring_nf
    _ ≥ 4 * (2 ^ (2 * n) - 2 ^ (n + 1)) + 2 * √(4^(n+1)) := by gcongr; linarith
    _ = 4 * (2 ^ (2 * n) - 2 ^ (n + 1)) + 2 * 2^(n+1) := by simp; rw [show (4:ℝ)=2^(2:ℝ) by norm_num, show ((2:ℝ) ^ (2:ℝ)) ^ (n + 1) = (2 ^ (2:ℝ)) ^ (n + 1:ℝ) by norm_cast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul, show ((2:ℝ) ^ (n + 1:ℝ)) ^ (2:ℝ) = (2 ^ (n + 1)) ^ (2:ℕ) by norm_cast, Real.sqrt_sq (by positivity)]; norm_cast;
    _ = 2^2 * (2 ^ (2 * n) - 2 ^ (n + 1)) + 2^(n+1+1) := by rw[show (4:ℝ)=2^(2:ℝ) by norm_num]; simp; ring_nf
    _ = 2 ^ (2 * (n + 1)) - 2 ^ (n + 1 + 1) := by ring_nf