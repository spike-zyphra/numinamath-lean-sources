import Mathlib

/- Solve the equation $\frac{p}{q}-\frac{4}{r+1}=1$ in prime numbers. -/
theorem number_theory_605061 :
    {(p, q, r) : ℕ × ℕ × ℕ | p.Prime ∧ q.Prime ∧ r.Prime ∧ (p / q : ℚ) - 4 / (r + 1 : ℚ) = 1} = {(3, 2, 7), (5, 3, 5), (7, 3, 2)} := by
  -- Simplify the goal into two parts.
  ext ⟨p, q, r⟩
  apply Iff.intro
  . -- Suppose (p, q, r) satisfies the given condition, we show that they belong to the three solutions.
    rintro ⟨hp, hq, hr, h⟩
    -- Rewrite the equation by clearing out denominators.
    field_simp [show (q : ℚ) ≠ 0 by by_contra!; simp at this; norm_num [this] at hq] at h
    replace h : r * (p - q) = (5 * q - p : ℤ) := by
      qify
      linarith
    -- We have p - kq ≠ 0 for all k ≥ 1.
    have h₀ (k : ℤ) (hk : k ≥ 1) : (p - k * q : ℤ) ≠ 0 := by
      by_contra! h₁
      -- Otherwise, q = kp, which will implies that p = q.
      have h₀ : p = q := by
        by_cases hk' : k = 1
        . -- Case k = 1.
          simp [hk'] at h₁
          zify
          linarith only [h₁]
        . -- Case k ≥ 2.
          apply eq_of_sub_eq_zero at h₁
          have h₀ : q ∣ p := by
            zify
            rw [h₁]
            apply dvd_mul_left
          rw [Nat.prime_dvd_prime_iff_eq hq hp] at h₀
          exact h₀.symm
      -- Now p = q, which implies that q = 5q by the equation, which is impossible.
      simp [h₀] at h
      linarith [show (q : ℤ) > 0 by by_contra!; simp at this; norm_num [this] at hq]
    -- From the equation, we get p - q ∣ 4q.
    rw [show (5 * q - p : ℤ) = 4 * q + -(p - q) by ring] at h
    have h₁ : (p - q : ℤ) ∣ 4 * q := by
      rw [@Int.dvd_iff_dvd_of_dvd_add _ _ (-(p - q)), Int.dvd_neg]
      rw [<-h]
      apply dvd_mul_left
    -- Show that q ∤ p - q.
    have h₂ : ¬(q : ℤ) ∣ (p - q : ℤ) := by
      -- Assume on the contrary that q ∣ (p - q : ℤ), then it contradicts with h₀ we proved above.
      by_contra! h₂
      obtain ⟨k, h₂⟩ := h₂
      -- Show that k ≥ 0.
      have h₃ : k ≥ 0 := by
        nlinarith [show (p : ℤ) > 0 by by_contra!; simp at this; norm_num [this] at hp]
      apply eq_add_of_sub_eq at h₂
      rw [<-mul_add_one] at h₂
      apply sub_eq_zero_of_eq at h₂
      absurd h₀ (k + 1)
      simp [h₃]
      rw [mul_comm, h₂]
    -- Hence, (p - q) and q are coprime.
    replace h₂ : IsCoprime (p - q : ℤ) (q : ℤ) := by
      apply IsCoprime.symm
      rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)]
      exact h₂
    -- Therefore, we have p - q ∣ 4.
    apply IsCoprime.dvd_of_dvd_mul_right h₂ at h₁
    obtain ⟨k, h₁⟩ := h₁
    -- Show that k > 0.
    have h₃ : k > 0 := by
      nlinarith
    -- We have k.natAbs ∣ 4, so k = 1, 2 or 4.
    have h₄ : k = 1 ∨ k = 2 ∨ k = 4 := by
      have h₄ : k.natAbs ∣ 4 := by
        zify
        simp
        rw [h₁]
        apply dvd_mul_left
      replace h₄ : k.natAbs ∈ Nat.divisors 4 := by
        simp [Nat.dvd_of_mem_divisors, h₄]
      rw [show Nat.divisors 4 = {1, 2, 4} by decide] at h₄
      simp at h₄
      zify at h₄
      simp [abs_of_nonneg (le_of_lt h₃)] at h₄
      exact h₄
    -- Show a lemma that consecutive primes with gap 1 must be 2 and 3.
    have h₅ {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (h : (p - q : ℤ) = 1) : p = 3 ∧ q = 2 := by
      apply eq_add_of_sub_eq at h
      norm_cast at h
      -- Show that q = 2.
      have h₀ : q = 2 := by
        -- Assume on the contrary that q > 2, then q is odd and p is hence even.
        by_contra! h₀
        have hq' := Nat.Prime.eq_two_or_odd' hq
        simp [h₀] at hq'
        have h₁ : Even p := by
          rw [h]
          apply Odd.add_odd (by use 0; rfl) hq'
          -- We have q = 2 but p > 2, contradicting our assumption.
        rw [even_iff_two_dvd, Nat.prime_dvd_prime_iff_eq (Nat.prime_two) hp] at h₁
        replace h₀ := lt_of_le_of_ne (Nat.Prime.two_le hq) h₀.symm
        linarith
      exact ⟨by linarith, h₀⟩
    -- Divide the cases according to possible values of k.
    rcases h₄ with (h₄ | h₄ | h₄)
    . -- This case corresponds to p - q = 4, which means p = 7, q = 3, r = 2.
      simp [h₄] at h₁
      simp [<-h₁] at h
      replace h : (q - r : ℤ) = 1 := by
        linarith
      specialize h₅ hq hr h
      simp [h₅.1] at h₁
      -- We have p = 7.
      replace h₁ : p = 7 := by
        zify
        linarith
      simp
      tauto
    . -- This case corresponds to p - q = 2, which means p = 5, q = 3, r = 5.
      simp [h₄] at h₁
      replace h₁ : (p - q : ℤ) = 2 := by
        linarith
      simp [h₁] at h
      replace h : 2 * q = r + 1 := by
        zify
        linarith
      -- We show that q = 3.
      replace h₅ : q = 3 := by
        -- Assume not, we try to derive a contradiction.
        by_contra! h₅
        -- Show that 3 ∤ q.
        have h₆ : ¬(q % 3 = 0) := by
          rw [<-Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq Nat.prime_three hq]
          tauto
        -- Show that 3 ∤ p.
        have h₇ : ¬(p % 3 = 0) := by
          by_contra! h₇
          rw [<-Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq Nat.prime_three hp] at h₇
          -- We cannot have p = 3, since otherwise q = 1.
          replace h₁ : q = 1 := by
            zify
            linarith
          norm_num [h₁] at hq
        apply eq_add_of_sub_eq at h₁
        norm_cast at h₁
        -- Then, we have 3 ∣ r by analyzing the conditions modulo 3.
        have h₈ : r % 3 = 0 := by
          replace h := congr_arg (· % 3) h
          simp at h
          rw [Nat.mul_mod, show q % 3 = 2 by omega] at h
          omega
        -- Then we have r = 3, q = 2, p = 4, contradiction.
        rw [<-Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq Nat.prime_three hr] at h₈
        norm_num [show p = 4 by linarith] at hp
      -- We have p = 5 and r = 5.
      have h₆ : p = 5 := by
        zify
        linarith
      have h₇ : r = 5 := by
        linarith
      simp
      tauto
    . -- This case corresponds to p - q = 1, which means p = 3, q = 2, r = 7.
      simp [h₄] at h₁
      rw [h₁] at h
      specialize h₅ hp hq h₁
      have h₆ : r = 7 := by
        zify
        linarith
      simp
      tauto
  . -- Show that the three solutions do satisfy the given condition.
    rintro (⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩)
    <;> norm_num