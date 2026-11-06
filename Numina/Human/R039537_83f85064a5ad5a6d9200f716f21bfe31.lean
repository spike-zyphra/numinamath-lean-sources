import Mathlib

open Nat

/- (Legendre's Formula) We denote $[x]$ as the integer part of the real number $x$. Show that if $p$ is a prime number and $n$ is a positive integer, we have:


$$

v_{p}(n!)=\sum_{i=1}^{\infty}\left[\frac{n}{p^{i}}\right]=\left[\frac{n}{p}\right]+\left[\frac{n}{p^{2}}\right]+\ldots

$$


When $p^{i}>n$, we have $\left[\frac{n}{p^{i}}\right]=0$. This ensures that there are only a finite number of non-zero terms in the sum above. -/
theorem number_theory_151066 (p n : ℕ) (hp : Nat.Prime p) :
    Nat.factorization (n !) p = ∑' i : ℕ, ⌊(n : ℝ) / p ^ (i + 1)⌋ := by
  -- we have (n !).factorization p = multiplicity p (n !)
  rw [←Nat.multiplicity_eq_factorization hp (Nat.factorial_ne_zero n)]
  -- we have Legendre's formula for computing emultiplicity p (n !)
  have eq := Nat.Prime.emultiplicity_factorial hp (Nat.lt_add_one (Nat.log p n))
  have hfin : FiniteMultiplicity p (n !) := by
    rw [finiteMultiplicity_iff]
    exact ⟨hp.ne_one, Nat.factorial_pos n⟩
  -- emultiplicity p (n !) = multiplicity p (n !) since the multiplicity of p in n ! is finite
  rw [hfin.emultiplicity_eq_iff_multiplicity_eq] at eq
  rw [eq]
  push_cast
  -- it is left to show that
  -- ∑ k ∈ [1, log p n + 1), n / p ^ k = ∑' i, ⌊(n : ℝ) / p ^ (i + 1)⌋
  -- show that (n : ℤ) / p ^ k = ⌊(n : ℝ) / p ^ k⌋
  have h (k : ℕ) : (n : ℤ) / p ^ k = ⌊(n : ℝ) / p ^ k⌋ := by
    rw [show (p ^ k : ℤ) = ((p ^ k : ℕ) : ℤ) by simp]
    rw [←Rat.floor_natCast_div_natCast]
    apply Int.floor_congr
    intro x
    rify
  -- rewrite the sum ∑ k ∈ [1, log p n + 1), n / p ^ k
  --               = ∑ k ∈ [0, log p n), ⌊(n : ℝ) / p ^ (k + 1)⌋
  simp_rw [h, Finset.sum_Ico_eq_sum_range, add_comm 1]
  symm
  -- it is left to show that ⌊(n : ℝ) / p ^ (k + 1)⌋ = 0 for k ≥ log p n
  apply tsum_eq_sum
  simp
  intro b hb
  -- show that 0 ≤ (n : ℝ) / p ^ (k + 1) < 1
  constructor
  · apply div_nonneg (by norm_num) (by norm_num)
  · have : 0 < (p : ℝ) ^ (b + 1) := by
      apply pow_pos
      norm_cast
      exact hp.pos
    rw [div_lt_one this]
    norm_cast
    -- we have n < n ^ (log p n + 1) ≤ n ^ (k + 1)
    apply lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt n)
    apply Nat.pow_le_pow_right hp.pos
    omega