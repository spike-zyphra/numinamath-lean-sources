import Mathlib

open Finset Real

/- ## Task 5 - 221245

Let $a_{1}, a_{2}, \ldots, a_{n}$ be real numbers. In an undisturbed technical process, let


$$

x_{1}=a_{1}+a_{2}+\ldots+a_{n}

$$


be the measurement of a quantity dependent on $a_{1}, a_{2}, \ldots, a_{n}$. In a disturbed technical process, the measurement of this quantity is instead


$$

x_{2}=\frac{a_{1}}{1+\epsilon_{1}}+\frac{a_{2}}{1+\epsilon_{2}}+\ldots+\frac{a_{n}}{1+\epsilon_{n}}

$$


Here, $\epsilon_{1}, \epsilon_{2}, \ldots, \epsilon_{n}$ are real numbers for which there exists a natural number $m \geq 1$ such that for all $\mu=1,2, \ldots, n$, the inequality $|\epsilon_{\mu}| \leq 10^{-m}$ (3) holds.

Prove that from these assumptions (1), (2), (3), the inequality


$$

\left|x_{2}-x_{1}\right| \leq \frac{1}{10^{m}-1}\left(\left|a_{1}\right|+\left|a_{2}\right|+\ldots+\left|a_{n}\right|\right)

$$


always follows! -/
theorem inequalities_198656 {n : ℕ} (hn : 0 < n) (hm : m ≥ 1) (a : Fin n → ℝ)
    (ε : Fin n → ℝ) (hε : ∀ i, |ε i| ≤ 10 ^ (-m : ℤ)) :
    |(∑ i : Fin n, a i / (1 + ε i)) - (∑ i : Fin n, a i)| ≤
    (1 / (10 ^ m - 1)) * ∑ i : Fin n, |a i| := by
  -- Bound size of ε i
  have ε_small : ∀ i, |ε i| < 1 := by
    intro i
    have : _ := hε i
    have : (10 : ℝ) ^ (-m) < 1 := by simp; rw [inv_lt_one₀ (by positivity)]; simp; linarith
    linarith
  -- Ensure denominator is nonzero
  have denom_nonzero : ∀ i, 1 + ε i ≠ 0 := by
    intro i h
    rw [← neg_eq_iff_add_eq_zero] at h
    have : |ε i| = 1 := by rw [← h]; norm_num
    linarith [ε_small i]
  -- Bound the residuals
  have res_bound : ∀ i, |1 - 1 / (1 + ε i)| ≤ 1 / (10 ^ m - 1) := by
    -- Absolute value inequality we will need to bound denominator
    have sub_abs_le_abs_add (y : ℝ) : 1 - |y| ≤ |1 + y| := by
      have : y ≤ 0 ∨ 0 ≤ y := by exact LinearOrder.le_total y 0
      -- Casework on whether y is negative or positive
      rcases this with neg | nonneg
      · rw [abs_eq_neg_self.mpr neg]
        simp
        exact le_abs_self (1 + y)
      rw [abs_eq_self.mpr nonneg]
      trans 1 + y
      · linarith
      exact le_abs_self (1 + y)
    intro i
    calc
      |1 - 1 / (1 + ε i)| = |(1 + ε i) / (1 + ε i) - 1 / (1 + ε i)| := by nth_rw 1 [← div_self (show 1 + ε i ≠ 0 by exact denom_nonzero i)]
      _ = |ε i / (1 + ε i)| := by rw [div_sub_div_same]; simp
      _ = |ε i| / |1 + ε i| := abs_div _ _
      _ ≤ |ε i| / (1 - |ε i|) := by refine div_le_div₀ (abs_nonneg _) (le_refl _) (by linarith [ε_small i]) (sub_abs_le_abs_add _)
      _ ≤ 10 ^ (-m) / (1 - |ε i|) := by rw [div_le_div_iff_of_pos_right (by linarith [ε_small i])]; exact hε i
      _ ≤ 10 ^ (-m) / (1 - 10 ^ (-m)) := by rw [div_le_div_iff_of_pos_left (by positivity) (by linarith [ε_small i]) (by simp; rw [inv_lt_one₀ (by positivity)]; simp; linarith)]; linarith [hε i]
      _ = (10 ^ (-m) * 10 ^ m) / ((1 - 10 ^ (-m)) * 10 ^ m) := (mul_div_mul_right (10 ^ (-m) : ℝ) (1 - 10 ^ (-m) : ℝ) (show (10 ^ m : ℝ) ≠ 0 by positivity)).symm
      _ = 1 / (10 ^ m - 1) := by rw [sub_mul, ← zpow_add₀]; simp; positivity
  -- Multiply res_bound by a i
  have bound : ∀ i, |a i / (1 + ε i) - a i| ≤ |a i| * (1 / (10 ^ m - 1)) := by
    intro i
    calc
      |a i / (1 + ε i) - a i| = |a i * (1 / (1 + ε i) - 1)| := by simp [mul_sub, div_eq_mul_inv]
      _ = |a i| * |1 / (1 + ε i) - 1| := abs_mul _ _
      _ = |a i| * |1 - 1 / (1 + ε i)| := by simp; left; exact abs_sub_comm _ _
      _ ≤ |a i| * (1 / (10 ^ m - 1)) := mul_le_mul_of_nonneg' (le_refl _) (res_bound _) (abs_nonneg _) (abs_nonneg _)
  -- Use the bound and triangle inequality to finish
  calc
    |(∑ i, a i / (1 + ε i)) - (∑ i, a i)| = |∑ i, (a i / (1 + ε i) - a i)| := by rw [sum_sub_distrib]
    _ ≤ ∑ i, |a i / (1 + ε i) - a i| := by exact abs_sum_le_sum_abs (fun i => a i / (1 + ε i) - a i) univ
    _ ≤ ∑ i, |a i| * (1 / (10 ^ m - 1)) := sum_le_sum fun i a => bound i
    _ = (1 / (10 ^ m - 1)) * ∑ i, |a i| := by rw [mul_comm]; exact Eq.symm (sum_mul univ (fun i => |a i|) (1 / (10 ^ m - 1)))