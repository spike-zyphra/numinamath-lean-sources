import Mathlib

/- Example 17 (1985 Bulgarian Mathematical Competition Problem) $k$ and $n$ are positive integers, prove that

$$
\left(n^{4}-1\right)\left(n^{3}-n^{2}+n-1\right)^{k}+(n+1) n^{4 k-1}
$$

is divisible by $n^{5}+1$. -/
theorem algebra_247138 (k : ℕ) (n : ℤ) (hk : 0 < k) :
    (n^4 - 1) * (n^3 - n^2 + n - 1)^k + (n + 1) * n^(4 * k - 1) ≡ 0 [ZMOD n^5 + 1] := by
    -- By induction on k
    induction k with
    -- k = 0 is not possible
    | zero => linarith
    | succ k ih =>
      if h : k = 0 then
        simp [h]
        -- base case k = 1: factor out (n^5 + 1)
        calc
          (n^4 - 1) * (n^3 - n^2 + n - 1) + (n + 1) * n^3 = (n^5 + 1) * (n^2 - n + 1) := by ring
          _ ≡ 0 [ZMOD (n^5 + 1)] := Int.modEq_zero_iff_dvd.mpr (by simp)
      else
        calc
          -- factor out inductive hypothesis part and (n^5 + 1) part
          (n^4 - 1) * (n^3 - n^2 + n - 1)^(k + 1) + (n + 1) * n^(4 * (k + 1) - 1)
          _ = (n^4 - 1) * (n^3 - n^2 + n - 1)^k * (n^3 - n^2 + n - 1) + (n + 1) * n^(4 * (k + 1) - 1) := by congr 1; ring
          _ = (n^4 - 1) * (n^3 - n^2 + n - 1)^k * (n^3 - n^2 + n - 1) + (n + 1) * (n^(4 * k - 1) * n^4) := by
            congr 1
            ring
            rw [Nat.add_sub_assoc]
            ring
            linarith [Nat.zero_lt_of_ne_zero h]
          _ = ((n^4 - 1) * (n^3 - n^2 + n - 1)^k + (n + 1) * n^(4 * k - 1)) * (n^3 - n^2 + n - 1) + (n^5 + 1) * n^(4 * k - 1)
          := by ring
          -- use inductive hypothesis on first half
          _ ≡ 0 * (n ^ 3 - n ^ 2 + n - 1) + (n^5 + 1) * n^(4 * k - 1) [ZMOD n ^ 5 + 1] := by
            apply Int.ModEq.add_right
            apply Int.ModEq.mul_right
            exact ih (Nat.zero_lt_of_ne_zero h)
          _ ≡ 0 * n^(4 * k - 1) [ZMOD n^5 + 1] := by
            simp
            have : (0 : ℤ) = 0 * n^(4*k - 1) := by simp
            rw [this]
            apply Int.ModEq.mul_right
            exact Int.modEq_zero_iff_dvd.mpr (by simp)
          _ ≡ 0 [ZMOD n^5 + 1] := by simp