import Mathlib

theorem number_theory_607520 (m n : ℤ): (0 ≤ m ∧ 0 ≤ n ∧ 1 + (m + n) * m ∣ (m + n) * (n + 1) - 1) ↔ (m = 0 ∧ 0 ≤ n ∨ m = 1 ∧ 0 ≤ n) := by
  constructor
  · -- Assume the divisibility holds, prove m = 0 or 1
    rintro ⟨hm, hn, h⟩
    have h1 : m ≥ 0 := by omega
    have h2 : n ≥ 0 := by omega
    -- Let k = m + n, then we have 1 + k*m divides k*(n+1) - 1
    -- We will show that 1 + k*m divides k*(k+1)
    have h3 : 1 + (m + n) * m ∣ (m + n) * (n + 1) - 1 := h
    -- Subsequently we can show that `1 + (m + n) * m` divides `(m + n) + 1`
    have h4 : 1 + (m + n) * m ∣ (m + n) * ((m + n) + 1) := by
      have h5 : 1 + (m + n) * m ∣ (m + n) * (n + 1) - 1 := h3
      have h6 : 1 + (m + n) * m ∣ 1 + (m + n) * m := by
        simp
      -- Now compute the difference.
      have h7 : 1 + (m + n) * m ∣ (m + n) * ((m + n) + 1) := by
        have eq1 : (m + n) * ((m + n) + 1) = ((m + n) * (n + 1) - 1) + (1 + (m + n) * m) := by
          nlinarith
        rw [eq1]
        apply Dvd.dvd.add
        · exact h3
        · exact h6
      exact h7
    -- We need to show that gcd(a,b) = 1, where a = 1 + (m + n) * m, b = m + n
    have h5 : IsCoprime (1 + (m + n) * m) (m + n) := by
      show IsCoprime (1 + (m + n) * m) (m + n)
      use 1, -m
      all_goals
      nlinarith
    have h33 : 1 + (m + n) * m ∣ (m + n) + 1 := by
      -- $\gcd(a, b) = 1$ and $a$ divides $b \cdot c$ implies $a$ divides $c$
      have h19 : IsCoprime (1 + (m + n) * m) (m + n) := h5
      replace h4 : 1 + (m + n) * m ∣ ((m + n) + 1) := by
        apply IsCoprime.dvd_of_dvd_mul_left h19
        exact h4
      exact h4
    have h34 : 1 + (m + n) * m ≤ (m + n) + 1 := by
      exact Int.le_of_dvd (show 0 < (m + n) + 1 by nlinarith) h33
    have h35 : m ≤ 1 := by
      nlinarith [sq_nonneg (m + n : ℤ), sq_nonneg (m : ℤ), sq_nonneg (n : ℤ)]
    have hm0 : m = 0 ∨ m = 1 := by
      omega
    tauto
  · -- Show the reverse direction
    rintro (h | h)
    · -- m = 0
      rcases h with ⟨rfl, hn⟩
      constructor
      · norm_num
      constructor
      · linarith
      · -- Show divisibility
        use (n * (n + 1) - 1)
        all_goals
          ring
    · -- m = 1
      rcases h with ⟨rfl, hn⟩
      constructor
      · norm_num
      constructor
      · linarith
      · -- Show divisibility
        use n
        all_goals
          nlinarith [sq_nonneg (n : ℤ)]