import Mathlib

/- 20. (1988 National High School Mathematics League) Given that $a$ and $b$ are positive real numbers, and $\frac{1}{a}+\frac{1}{b}=1$, prove that for every $n \in \mathbf{N}^{*}$, we have

$$

(a+b)^{n}-a^{n}-b^{n} \geqslant 2^{2 n}-2^{n+1} .

$$
 -/
theorem inequalities_194663 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a + 1 / b = 1) (n : ℕ) (hn : 0 < n) :
    (a + b) ^ n - a ^ n - b ^ n ≥ 2 ^ (2 * n) - 2 ^ (n + 1) := by
  -- let's get an estimate for the rhs with binomial theorem
  have h0:(a + b) ^ n - a ^ n - b ^ n = ∑ k ∈ Finset.Ico 1 n, a ^ k * b ^ (n - k) * ↑(n.choose k) := by
    rw [add_pow, Finset.sum_range_eq_add_Ico, Finset.sum_Ico_succ_top]; simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_self, Nat.sub_zero, Nat.sub_self]
    rw [add_sub_assoc, add_comm (b^n), add_sub_assoc, sub_self, add_zero, add_sub_assoc, sub_self, add_zero]
    rotate_left; omega; omega
  -- we can also use nCk = nC(n-k)
  have h1: (a+b)^n - a^n - b^n = ∑ k ∈ Finset.Ico 1 n, a ^ k * b ^ (n - k) * ↑(n.choose (n-k)) := by
    rw [h0]
    apply Finset.sum_congr rfl
    intro k hk; simp at hk
    rw [Nat.choose_symm (by linarith)]
  -- if we rotate the index, we'll then be able to group the sums by nCk
  have h1': ∑ k ∈ Finset.Ico 1 n, a ^ k * b ^ (n - k) * ↑(n.choose (n-k)) = ∑ k ∈ Finset.Ico 1 n, a ^ (n-k) * b ^ k * ↑(n.choose k) := by
    have h3:= Finset.sum_Ico_reflect (k:=1) (m:=n) (n:=n) (f:=fun k=>a ^ k * b ^ (n - k) * ↑(n.choose (n - k))) (by linarith)
    simp at h3; rw[← h3]
    apply Finset.sum_congr rfl
    intro k hk; simp at hk
    rw [show n-(n-k)=k by omega, Nat.choose_symm (by linarith)]
  -- we can add the two sums together
  have h2:(a+b)^n-a^n-b^n + (a+b)^n-a^n-b^n = ∑ k ∈ Finset.Ico 1 n, a ^ k * b ^ (n - k) * ↑(n.choose k) + ∑ k ∈ Finset.Ico 1 n, a ^ (n-k) * b ^ k * ↑(n.choose k) := by linarith
  rw [show ((a+b)^n-a^n-b^n + (a+b)^n-a^n-b^n) = 2*((a+b)^n-a^n-b^n) by ring, ← Finset.sum_add_distrib] at h2
  apply congr_arg (fun t =>t/2) at h2
  rw [mul_comm, ← mul_div, div_self (by norm_num), mul_one, Finset.sum_div] at h2
  -- now we need to find a bound for √(a*b)
  have hab: 2≤√(a*b) := by
    -- we use am-hm
    have hmgm:∀ x y:ℝ, 0<x → 0<y → 2*x*y/(x+y) ≤ √(x*y) := by
      intro x y hx hy
      refine (Real.le_sqrt' ?_).mpr ?_
      positivity; rw [div_pow]
      refine (div_le_iff₀' ?_).mpr ?_
      positivity
      suffices 0 ≤ (x + y) ^ 2 * (x * y) - (2*x*y)^2 by linarith
      rw [show (x + y) ^ 2 * (x * y) - (2 * x * y) ^ 2 = (x*y)*(x-y)^2 by ring_nf]
      positivity
    specialize hmgm a b ha hb
    suffices a * b / (a + b) = 1/(1/a + 1/b) by rw [mul_assoc, ← mul_div, this, h, div_one,  mul_one] at hmgm; exact hmgm
    field_simp; ring_nf
  -- now we can simplify at h2
  conv_rhs at h2 =>
    rhs; intro i
    rw [← add_mul, mul_comm, ← mul_div]
  rw [h2]
  -- we assemble the result
  calc ∑ i ∈ Finset.Ico 1 n, ↑(n.choose i) * ((a ^ i * b ^ (n - i) + a ^ (n - i) * b ^ i) / 2)
    _ ≥ ∑ i ∈ Finset.Ico 1 n, ↑(n.choose i) * √(a ^ i * b ^ (n - i) * a ^ (n - i) * b ^ i) := by
      apply Finset.sum_le_sum; intro i hi; simp at hi
      gcongr
      -- AMGM
      have q:= Real.geom_mean_le_arith_mean2_weighted (w₁:=1/2) (w₂:=1/2) (p₁:=a ^ i * b ^ (n - i)) (p₂:=a ^ (n - i) * b ^ i) (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
      rw [← mul_add, mul_comm (1/2), mul_div, mul_one, ← Real.mul_rpow (by positivity) (by positivity), ← Real.sqrt_eq_rpow, ← mul_assoc] at q
      exact q
    _ = ∑ i ∈ Finset.Ico 1 n, ↑(n.choose i) * √(a ^ n * b ^ n) := by apply Finset.sum_congr; rfl; intro i hi; simp at hi; simp; left; apply congr_arg; ring_nf; rw [← pow_add, show i + (n - i)=n by omega, mul_assoc, ← pow_add, show i+(n-i)=n by omega]
    _ = ∑ i ∈ Finset.Ico 1 n, ↑(n.choose i) * √(a * b)^n := by apply Finset.sum_congr; rfl; intro i hi; simp at hi; simp; left; rw [← mul_pow, Real.sqrt_eq_rpow, show (a * b) ^ n=(a * b) ^ (n:ℝ) by norm_cast, ← Real.rpow_mul (by positivity), mul_comm (n:ℝ), Real.rpow_mul (by positivity), ← Real.sqrt_eq_rpow]; norm_cast
    _ ≥ ∑ i ∈ Finset.Ico 1 n, ↑(n.choose i) * 2^n := by apply Finset.sum_le_sum; intro i hi; simp at hi; gcongr
    _ = 2^n * (∑ i ∈ Finset.Ico 1 n, n.choose i) := by rw [← Finset.sum_mul, mul_comm]; norm_cast
    _ = 2^n * ((∑ i ∈ Finset.range (n+1), n.choose i) - 2) := by
      simp; rw [Finset.sum_range_eq_add_Ico, Finset.sum_Ico_succ_top]
      simp; ring_nf; omega; omega
    -- binomials sum to 2^n
    _ = 2^n * (2^n-2) := by rw [Nat.sum_range_choose]; norm_cast
    _ = 2 ^ (2 * n) - 2 ^ (n + 1) := by ring_nf