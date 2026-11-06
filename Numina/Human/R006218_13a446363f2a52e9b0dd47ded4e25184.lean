import Mathlib
/- Let $k$ be an integer base, $k > 3$. Let $A, B, C$ be integers such that $k > A > B > C > 0$.
The notation $\overline{XYZ}_k$ denotes the number $X k^2 + Y k + Z$.
Suppose that the following equation holds:
$$ \overline{ABC}_k - \overline{CBA}_k = \overline{BAC}_k $$
Show that this implies $(k^2-k-1)A = (B+C)k^2$. Further, show that this equation has no solution for $A, B, C$ satisfying the given constraints. -/
theorem number_theory_634778 (k A B C : ℤ) (hk : k > 3) (h1 : k > A) (h2 : A > B) (h3 : B > C) (h4 : C > 0) (h5 : A * k ^ 2 + B * k + C - (C * k ^ 2 + B * k + A) = B * k ^ 2 + A * k + C) : (k ^ 2 - k - 1) * A = (B + C) * k ^ 2 ∧ False:= by
  -- Construct the conjunction proof
  constructor
  -- First part: Prove (k^2 - k - 1)A = (B + C)k^2 using linear arithmetic
  .
    linarith
  -- Second part: Prove that no solution exists
  .
    -- Prove that (k + 1)A = (A - B - C)k^2
    have h : (k + 1) * A = (A - B - C) * k ^ 2:= by linarith
    -- Prove that k + 1 and k are coprime
    have g : IsCoprime (k + 1) k:= by
      simp [IsCoprime]
      use 1, -1
      simp
    -- Extend coprimality to k^2
    replace g : IsCoprime (k + 1) (k ^ 2):= by exact IsCoprime.pow_right g
    -- Show that k^2 divides (k + 1)A
    replace h : k ^ 2 ∣ (k + 1) * A:= by rw [h] ; simp
    -- Use coprimality to show k^2 divides A
    replace h : k ^ 2 ∣ A:= by exact IsCoprime.dvd_of_dvd_mul_left (id (IsCoprime.symm g)) h
    -- Prove A is not zero
    have g1 : A ≠ 0:= by
      by_contra H
      linarith
    -- Show that absolute value of k^2 is less than or equal to absolute value of A
    replace h : (k ^ 2).natAbs ≤ A.natAbs:= by refine Int.natAbs_le_of_dvd_ne_zero h g1
    -- Convert to integer arithmetic
    zify at h
    -- Handle absolute value with non-negative numbers
    rw [abs_of_nonneg (by positivity)] at h
    rw [abs_of_nonneg (by linarith)] at h
    -- Prove k is at least 4
    have g2 : k ≥ 4:= by linarith
    -- Show k * k ≥ 4 * k
    replace g2 : k * k ≥ 4 * k:= by
      replace hk : k ≥ 0:= by linarith
      exact Int.mul_le_mul_of_nonneg_right g2 hk
    -- Complete the proof using linear arithmetic
    linarith
