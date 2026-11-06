import Mathlib

/-For what base is the representation of $285_{10}$ a four digit number whose final digit is odd?-/
theorem number_theory_11162 (n : ℕ) (h₀ : n > 1)
    (h₁ : (n.digits 285).length = 4) (h₂ : Odd (n.digits 285).head!) : n = 6 := by
  -- $285_{10}$ is only four digits for bases 5 and 6, since only these two bases satisfy $b^{4}>285_{10}\geq b^{3}$.
  have p : 285 < n^4 := by
    rw [h₁.symm]
    apply Nat.lt_base_pow_length_digits
    exact h₀
  have q : n^4 ≤ n * 285 := by
    rw [h₁.symm]
    apply Nat.base_pow_length_digits_le
    repeat linarith
  by_cases h₃ : n ≥ 7
  . -- it conficts with q: `n^4 ≤ n * 285`
    have : n * 285 < n * n^3 := by
      have : 7^3 ≤ n^3 := by
          exact Nat.pow_le_pow_of_le_left h₃ 3
      apply Nat.mul_lt_mul_of_le_of_lt
      repeat linarith
    linarith
  have h₃ : n ≤ 6 := by linarith
  by_cases h₄ : n ≤ 4
  . -- it conflicts with p: `285 < n^4`
    linarith [Nat.pow_le_pow_of_le_left h₄ 4]
  have h₄ : n ≥ 5 := by linarith
  by_cases h₅ : 5 = n
  . -- Testing each of our two cases, we find that $285_{10}= 2120_{5} = 1153_{6}$, so only base $\boxed{6}$ yields a four-digit representation with an odd units digit.
    rw [h₅.symm] at h₂
    -- h₂: Odd 0, which is impossible
    absurd h₂
    norm_num
  have h₄ : 5 < n := by apply Nat.lt_of_le_of_ne h₄ h₅
  exact Nat.le_antisymm h₃ h₄