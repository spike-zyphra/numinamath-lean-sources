import Mathlib

/- Find the smallest positive integer $n$ such that $1^{2}+2^{2}+3^{2}+4^{2}+\cdots+n^{2}$ is divisible by 100 .-/
theorem number_theory_611149 :
    IsLeast {n : ℕ | 0 < n ∧ 100 ∣ ∑ i ∈ Finset.Icc 1 n, i ^ 2} 24 := by
  -- First show that ∑ i ∈ Finset.Icc 1 n, i ^ 2 = n * (n + 1) * (2 * n + 1) / 6.
  have h₁ (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, (i ^ 2 : ℕ) = (n * (n + 1) * (2 * n + 1) / 6 : ℚ) := by
    induction n with
    | zero =>
      simp
    | succ n hn =>
      rw [Finset.sum_Icc_succ_top]
      push_cast at hn ⊢
      rw [hn]
      ring
      omega
  -- Simplify the goal in two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_,?_⟩
  . -- First show that 100 ∣ ∑ i ∈ Finset.Icc 1 24, i ^ 2.
    specialize h₁ 24
    norm_cast at h₁
  . -- Now show that 24 is the smallest positive integer such that 100 ∣ ∑ i ∈ Finset.Icc 1 n, i ^ 2.
    intro n hn h
    specialize h₁ n
    rw [eq_div_iff (by norm_num)] at h₁
    norm_cast at h₁
    -- Show that n(n+1)(2n+1) is divisible by 600.
    have h₂ : 600 ∣ n * (n + 1) * (2 * n + 1) := by
      calc
        600 = 100 * 6 := by norm_num
        _ ∣ (∑ i ∈ Finset.Icc 1 n, i ^ 2) * 6 := Nat.mul_dvd_mul_right h 6
        _ = n * (n + 1) * (2 * n + 1) := h₁
    -- We have either 25 ∣ n, 25 ∣ n + 1 or 25 ∣ 2n + 1, because the three factors are mutually coprime.
    have h₃ : 25 ∣ n ∨ 25 ∣ n + 1 ∨ 25 ∣ 2 * n + 1 := by
      -- Assume on the contrary that neither of them is divisible by 25.
      by_contra! h₃
      replace h₂ : 25 ∣ n * (n + 1) * (2 * n + 1) := by
        calc
          25 ∣ 600 := by norm_num
          _ ∣ n * (n + 1) * (2 * n + 1) := h₂
      apply Nat.Coprime.dvd_of_dvd_mul_right at h₂
      apply Nat.Coprime.dvd_of_dvd_mul_right at h₂
      absurd h₃.1
      exact h₂
      -- Verfiy that 25 and n + 1 is coprime.
      . rw [show 25 = 5 ^ 2 by norm_num] at h₂ ⊢
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd (Nat.prime_five)]
        by_contra! h₄
        -- Assume 5 ∣ n + 1, then neither 5 ∣ n nor 5 ∣ 2n + 1.
        have h₅ : ¬5 ∣ n := by
          by_contra! h₅
          -- We have 5 ∣ 1, a contradiction.
          rw [<-Nat.dvd_add_iff_right h₅] at h₄
          norm_num at h₄
        -- We then have 25 ∣ n + 1.
        apply Prime.pow_dvd_of_dvd_mul_left (Nat.prime_iff.mp Nat.prime_five) _ h₅ at h₂
        absurd h₃.2.1
        simp_all
      . -- Verify that 25 and 2n + 1 is coprime.
        rw [show 25 = 5 ^ 2 by norm_num] at h₂ ⊢
        apply Nat.Coprime.pow_left
        rw [Nat.Prime.coprime_iff_not_dvd (Nat.prime_five)]
        by_contra! h₄
        -- Assume 5 ∣ 2n + 1, then neither 5 ∣ n nor 5 ∣ n + 1.
        have h₅ : ¬5 ∣ n := by
          by_contra! h₅
          rw [show 2 * n + 1 = n + (n + 1) by ring] at h₄
          iterate 2 rw [<-Nat.dvd_add_iff_right h₅] at h₄
          -- We have 5 ∣ 1, a contradiction.
          norm_num at h₄
        have h₆ : ¬5 ∣ n + 1 := by
          by_contra! h₆
          rw [show 2 * n + 1 = n + (n + 1) by ring] at h₄
          rw [<-Nat.dvd_add_iff_left h₆] at h₄
          contradiction
        -- We then have 25 ∣ 2n + 1.
        apply Prime.pow_dvd_of_dvd_mul_left (Nat.prime_iff.mp Nat.prime_five) at h₂
        simp_all
        by_contra! h₇
        rw [Nat.Prime.dvd_mul (Nat.prime_five)] at h₇
        tauto
    -- Consider cases of 25 ∣ n, 25 ∣ n + 1 and 25 ∣ 2n + 1.
    obtain h₃ | h₃ | h₃ := h₃
    . -- If 25 ∣ n, then obviously 24 ≤ n.
      apply Nat.le_of_dvd hn at h₃
      omega
    . -- If 25 ∣ n + 1, then 25 ≤ n + 1 and 24 ≤ n.
      apply Nat.le_of_dvd (by omega) at h₃
      omega
    . -- If 25 ∣ 2n + 1, then n = 12 or 24 ≤ n.
      have h₄ := Nat.le_of_dvd (by omega) h₃
      by_cases h₅ : n = 12
      . -- If n = 12, it does not work by directly justifying.
        rw [h₅] at h₂
        norm_num at h₂
      . -- If n ≠ 12, then 24 ≤ n.
        omega
