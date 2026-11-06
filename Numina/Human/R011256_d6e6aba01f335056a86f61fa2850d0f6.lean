import Mathlib

/-Prove that

$$
\frac{\sigma(1)}{1}+\frac{\sigma(2)}{2}+\frac{\sigma(3)}{3}+\cdots+\frac{\sigma(n)}{n} \leq 2 n
$$

for every positive integer $n$.-/
theorem number_theory_611302 : ∀ n : ℕ, n > 0 → ∑ k in Finset.Icc 1 n, (((ArithmeticFunction.sigma 1) k) / k : ℝ) ≤ 2 * n := by
  intro n hn
  -- This is similar to the previous solution.
  -- If $d$ is a divisor of $i$, then so is $i / d$, and $(i / d) / i=1 / d$.
  -- Summing over all $d$, we see that $\sigma(i) / i$ is the sum of the reciprocals of the divisors of $i$, for each positive integer $i$.
  have h1 : ∑ k in Finset.Icc 1 n, (((ArithmeticFunction.sigma 1) k) / k : ℝ) =
    ∑ k in Finset.Icc 1 n, (Finset.sum (Nat.divisors k) (fun i => (1 / i : ℝ))) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors,Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have : (↑(x / d):ℝ) = ↑x / ↑d := by
      refine Nat.cast_div ?_ ?_
      exact Nat.dvd_of_mem_divisors hd
      simp ;refine Nat.ne_zero_iff_zero_lt.mpr ?_
      exact Nat.pos_of_mem_divisors hd
    rw [this,div_div,div_mul_cancel_right₀]
    simp ;simp at hx ;simp ;linarith
  --  So, summing over all $i$ from 1 to $n$, we get the value $1 / d$ appearing $\lfloor n / d\rfloor$ times, once for each multiple of $d$ that is at most $n$.
  have h2 : ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ k.divisors, (1 / ↑i :ℝ) =
    ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ (Finset.filter (fun p => p ≠ 0 ∧ i∣p) (Finset.range (Nat.succ n))), 1 / (↑ i:ℝ) := by
    apply Finset.sum_comm'
    intro x y ;constructor ;intro ⟨hx,hy⟩
    constructor
    · simp ;simp at hx ;constructor ;linarith ;constructor ;linarith
      exact Nat.dvd_of_mem_divisors hy
    simp ;simp at hx ;constructor
    refine Nat.one_le_iff_ne_zero.mpr ?_
    refine Nat.ne_zero_iff_zero_lt.mpr ?_ ;exact Nat.pos_of_mem_divisors hy
    have : y ≤ x := by exact Nat.divisor_le hy
    linarith
    intro ⟨hx,hy⟩ ;simp at hx hy
    constructor ;simp ;constructor ;refine Nat.one_le_iff_ne_zero.mpr ?_
    simp ;exact hx.2.1 ;linarith ;refine Nat.mem_divisors.mpr ?_ ;simp [hx]
  -- In particular, the sum is
  -- $$ \frac{1}{1}\left\lfloor\frac{n}{1}\right\rfloor+\frac{1}{2}\left\lfloor\frac{n}{2}\right\rfloor+\frac{1}{3}\left\lfloor\frac{n}{3}\right\rfloor+\cdots+\frac{1}{n}\left\lfloor\frac{n}{n}\right\rfloor&lt;\frac{n}{1^{2}}+\frac{n}{2^{2}}+\cdots+\frac{n}{n^{2}} . $$
  have h3 : ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ (Finset.filter (fun p => p ≠ 0 ∧ i∣p) (Finset.range (Nat.succ n))), 1 / (↑ i:ℝ) ≤
    ∑ i ∈ Finset.Icc 1 n, (n / (i * i : ℝ)) := by
    apply Finset.sum_le_sum
    simp
    intro x hx hx'
    rw [Nat.card_multiples']
    have : (n / (x * x : ℝ)) = (n / x : ℝ) * (1 / ↑x) := by field_simp
    rw [this] ;simp ;apply (mul_le_mul_right (?_)).mpr
    exact Nat.cast_div_le ;simp ;linarith
  -- So now all we need is $1 / 1^{2}+1 / 2^{2}+\cdots+1 / n^{2}&lt;2$.
  -- This can be obtained from the classic formula $1 / 1^{2}+1 / 2^{2}+\cdots=\pi^{2} / 6$, or from the more elementary estimate
  -- $$ \begin{aligned} 1 / 2^{2}+1 / 3^{2}+\cdots+1 / n^{2} & &lt;1 /(1 \cdot 2)+1 /(2 \cdot 3)+\cdots+1 /((n-1) \cdot n) \ & =(1 / 1-1 / 2)+(1 / 2-1 / 3)+\cdots+(1 /(n-1)-1 / n) \ & =1-1 / n \ & &lt;1 . \end{aligned} $$
  have h4 : ∑ i ∈ (Finset.Icc 1 n), (fun (p : ℕ) ↦ (1 / (p ^ 2):ℝ)) i ≤ (Real.pi ^ 2 / 6) := by
    apply sum_le_hasSum
    simp
    exact hasSum_zeta_two
  have h5 : ∑ i ∈ Finset.Icc 1 n, (n / (i * i : ℝ)) = ∑ i ∈ Finset.Icc 1 n, (n * (1 / (i ^ 2 : ℝ))) := by
    apply Finset.sum_congr rfl
    intro x hx
    field_simp [pow_two]
  rw [← Finset.mul_sum] at h5
  have h6 : ∑ i ∈ Finset.Icc 1 n, (1 / (i ^ 2 : ℝ)) = ∑ i ∈ (Finset.Icc 1 n), (fun (p : ℕ) ↦ (1 / (p ^ 2):ℝ)) i := by
    apply Finset.sum_congr rfl
    intro x hx
    simp
  have h7 : Real.pi ^ 2 / 6 ≤ 2 := by
    have : Real.pi < 3.15 := Real.pi_lt_d2
    have : Real.pi ^ 2 < 3.15 ^ 2 := by
      refine (sq_lt_sq₀ (Real.pi_nonneg) (by norm_num)).mpr this
    have : Real.pi ^ 2 / 6 < 3.15 ^ 2 / 6 := by
      refine div_lt_div_of_pos_right this (by norm_num)
    norm_num at this
    linarith
  rw [h1,h2] ;rw [h5] at h3
  have h8 : ↑n * (∑ i ∈ (Finset.Icc 1 n), (fun (p : ℕ) ↦ (1 / (p ^ 2):ℝ)) i) ≤ 2 * n := by
    rw [mul_comm,mul_le_mul_right] ;linarith ;simp ;linarith
  linarith