import Mathlib

/- $2+$ [ Factorization ]

After the lesson, Oleg bet with Sasha, claiming that he knows a natural number $m$, such that the number $m / 3 + m^{2} / 2 + m^{3} / 6$ is not an integer. Is Oleg right? And if he is, what is this number?-/
theorem number_theory_233412 :
    ¬∃ m : ℕ, ¬∃ k : ℕ, (m / 3 + m ^ 2 / 2 + m ^ 3 / 6 : ℚ) = k := by
  rintro ⟨m, hm⟩
  simp at hm
  -- We show that 6 ∣ m(m+1)(m+2).
  have h₀ : 2 * 3 ∣ m * (m + 1) * (m + 2) := by
    -- It suffices to show that both 2 and 3 divides the right hand side, since 2 and 3 are coprime.
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    <;> rw [Nat.dvd_iff_mod_eq_zero]
    . -- We have m % 2 = 0 or 1. For either cases, the statement holds.
      have h₁ : m % 2 = 0 ∨ m % 2 = 1 := by
        omega
      rcases h₁ with (h₁ | h₁)
      <;> simp [Nat.add_mod, Nat.mul_mod, h₁]
    . have h₁ : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
        omega
      rcases h₁ with (h₁ | h₁ | h₁)
      <;> simp [Nat.add_mod, Nat.mul_mod, h₁]
  -- Let k = m(m+1)(m+2) / 6.
  obtain ⟨k, h₀⟩ := h₀
  -- Use k in the hypothesis, which is a contradiction.
  absurd hm k
  qify at h₀
  linarith