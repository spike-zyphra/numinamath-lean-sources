import Mathlib

/- Consider the infinite arithmetic sequence $A$ with first term $5$ and common difference $-2$. Now define the infinite sequence $B$ so that the $k^{th}$ term of $B$ is $2$ raised to the $k^{th}$ term of $A$. Find the sum of all of the terms of $B$. -/
theorem algebra_20873 (A B : ℕ → ℝ) (hA : ∀ n : ℕ, A n = 5 - 2 * ↑n) (hB : ∀ n : ℕ, B n = 2 ^ A n): ∑' n, B n = 128 / 3 := by
  simp [hA] at hB  
  simp [hB]        
  -- 证明对任意 n，2^(5-2n) = 32 * (1/4)^n
  have h : ∀ n : ℕ, 2 ^ ((5 : ℝ) - 2 * ↑n) = (32 : ℝ) * (1 / 4) ^ n:= by
    intro n
    -- 证明 2n ≠ 5
    have g1 : 2 * n ≠ 5:= by
      by_contra H
      have H1 : 2 ∣ 2 * n:= by exact Nat.dvd_mul_right 2 n
      rw [H] at H1
      omega
    rify at g1
    -- 证明 5-2n ≠ 0
    have g2 : (5 : ℝ) - 2 * ↑n ≠ 0:= by
      by_contra!
      replace this : (2 : ℝ) * ↑n = 5:= by linarith
      trivial
    -- 使用指数的加法法则
    have h1 : (2 : ℝ) ^ ((5 : ℝ) - 2 * ↑n) = 2 ^ (5 : ℝ) * 2 ^ ((-2 : ℝ) * ↑n):= Real.rpow_of_add_eq (by linarith) g2 (by linarith)
    rw [h1]
    rw [show (2 : ℝ) ^ (5 : ℝ) = 32 by norm_num]  -- 计算 2^5 = 32
    -- 使用指数的乘法法则
    have g3 : (2 : ℝ) ^ ((-2 : ℝ) * ↑n) = ((2 : ℝ) ^ (-2 : ℝ)) ^ (↑n : ℝ):= Real.rpow_mul (by linarith) (-2) ↑n
    rw [g3]
    rw [show ((2 : ℝ) ^ (-2 : ℝ)) = 1 / 4 by norm_num]  -- 计算 2^(-2) = 1/4
    have g4 : ((1 : ℝ) / 4) ^ n = ((1 : ℝ) / 4) ^ (↑n : ℝ):= by norm_cast
    rw [g4]
  simp [h]
  ring_nf
  -- 使用级数的乘法分配律
  have h1 : ∑' (n : ℕ), ((1 : ℝ) / 4) ^ n * 32 = (∑' (n : ℕ), ((1 : ℝ) / 4) ^ n) * 32:= tsum_mul_right
  rw [h1]
  clear h1
  -- 证明 |1/4| = 1/4
  have h1 : |(1 : ℝ) / 4| = 1 / 4:= by norm_num
  -- 使用等比级数求和公式，当|r|<1时，∑r^n = 1/(1-r)
  have h2 : (∑' (n : ℕ), ((1 : ℝ) / 4) ^ n) = (1 - 1 / 4)⁻¹:= tsum_geometric_of_abs_lt_one (by linarith)
  rw [h2]
  -- 计算最终结果 128/3
  norm_num  
