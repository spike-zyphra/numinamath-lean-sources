import Mathlib

/- Let $p$ be an odd prime. Find all positive integers $n$ for which $\sqrt{n^{2}-n p}$ is a positive integer. -/
theorem number_theory_238413 (p : ℕ) (hp : Odd p ∧ Nat.Prime p) :
    {n : ℕ | 0 < n ∧ ∃ k : ℕ, 0 < k ∧ Real.sqrt (n ^ 2 - n * p) = k} = {((p + 1) / 2) ^ 2} := by
  -- Break the goal into two parts.
  ext n
  apply Iff.intro
  . -- First show that the condition implies that n = ((p + 1) / 2)².
    simp
    -- Suppose √(n² - pn) = m is a positive integer.
    intro hn m hm h₀
    -- Justify that 0 ≤ n² - np, otherwise it doesn't make sense.
    have h₁ : 0 ≤ (n ^ 2 - n * p : ℝ) := by
      by_contra!
      apply le_of_lt at this
      rw [<-Real.sqrt_eq_zero'] at this
      rw [this] at h₀
      norm_cast at h₀
      nlinarith
    -- We have n² - pn - m = 0.
    rw [<-sq_eq_sq₀ (by positivity) (by positivity), Real.sq_sqrt h₁] at h₀
    -- Continue with the goal and rewrite this as a quadratic equation in terms of n
    replace h₀ : (2 * n - p : ℝ) ^ 2 = p ^ 2 + 4 * m ^ 2 := by
      linarith only [h₀]
    norm_cast at h₀
    qify at h₀
    -- Note that p² + 4m² is now a square.
    have h₂ : IsSquare ((p ^ 2 + 4 * m ^ 2 : ℕ) : ℚ) := by
      simp [<-h₀]
      simp [pow_two, IsSquare]
      use (2 * n - p : ℚ)
    rw [Rat.isSquare_natCast_iff] at h₂
    simp [IsSquare] at h₂
    -- Let p² + 4m² = k² for some k ∈ ℕ.
    obtain ⟨k, h₂⟩ := h₂
    -- Substitute h₂ into h₀.
    qify at h₂
    rw [h₂, <-pow_two] at h₀
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h₀
    -- We have two cases to consider.
    cases h₀ with
    | inl h₀ =>
      -- We have 2n - p = k.
      -- Rearrange h₂ to get p² = k² - 4m² = (k + 2m)(k - 2m).
      have h₃ : p ^ 2 = (k + 2 * m) * (k - 2 * m) := by
        zify
        rw [<-@Int.subNatNat_of_le k (2 * m)]
        qify
        linarith
        -- Verify that k ≥ 2m.
        qify
        rw [<-sq_le_sq₀ (by positivity) (by positivity)]
        linarith [show (p : ℚ) ^ 2 ≥ 0 by positivity]
      -- Note that p is a prime, so the only possible factorization is k + 2m = p² and k - 2m = 1.
      have h₄ : (k + 2 * m) ∈ (p ^ 2).divisors := by
        simp [Nat.divisors]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        . -- Show that 1 ≤ k + 2m.
          by_contra!
          simp at this
          simp [this.1, this.2] at h₃
          omega
        . -- Show that k + 2m ≤ p².
          apply Nat.lt_add_one_of_le
          apply Nat.le_of_dvd
          . by_contra!
            simp at this
            norm_num [this] at hp
          . rw [h₃]
            exact Nat.dvd_mul_right _ _
        . -- Show that k + 2m ∣ p².
          rw [h₃]
          exact Nat.dvd_mul_right _ _
      have h₅ : (k - 2 * m) ∈ (p ^ 2).divisors := by
        simp [Nat.divisors]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        . -- Show that 1 ≤ k - 2m.
          by_contra!
          simp at this
          simp [this, this] at h₃
          norm_num [h₃] at hp
        . -- Show that k - 2m ≤ p².
          apply Nat.lt_add_one_of_le
          apply Nat.le_of_dvd
          . by_contra!
            simp at this
            norm_num [this] at hp
          . rw [h₃]
            exact Nat.dvd_mul_left _ _
        . -- Show that k - 2m ∣ p².
          rw [h₃]
          exact Nat.dvd_mul_left _ _
      -- Show that (k + 2m) and (k - 2m) are both powers of p.
      rw [Nat.mem_divisors_prime_pow hp.2] at h₄ h₅
      obtain ⟨c, ⟨hc, h₄⟩⟩ := h₄
      obtain ⟨d, ⟨hd, h₅⟩⟩ := h₅
      -- We have d < c.
      have h₆ : d < c := by
        rw [<-@Nat.pow_lt_pow_iff_right p, <-h₄, <-h₅]
        omega
        exact Nat.Prime.one_lt hp.2
      interval_cases c
      . -- c = 0 is impossible.
        omega
      . -- c = 1 is impossible.
        interval_cases d
        . -- We have c = 1 and d = 0, and hence p² = p, contradiction.
          rw [h₄, h₅] at h₃
          norm_num at h₃
          replace hp := (hp.2)
          rw [<-h₃, pow_two] at hp
          apply Nat.not_prime_mul at hp
          tauto
          all_goals
            by_contra!
            simp [this] at hp
            absurd hp
            exact Nat.not_prime_one
      . -- Now c = 2.
        interval_cases d
        . -- We have d = 0, which is correct.
          -- Now (k + 2m, k - 2m) = (p², 1), and we solve for n.
          replace h₀ := congr_arg (2 * ·) h₀
          simp only at h₀
          zify at h₅
          rw [<-Int.subNatNat_of_le] at h₅
          qify at h₄ h₅
          rw [show (2 * k : ℚ) = (k + 2 * m : ℚ) + (k - 2 * m : ℚ) by ring, h₄, h₅, mul_sub, sub_eq_iff_eq_add] at h₀
          -- Now 4n = (p + 1)².
          replace h₀ : 4 * n = (p + 1) ^ 2 := by
            norm_cast at h₀
            linarith
          -- Note that p + 1 is even, so n = ((p + 1) / 2)².
          have hp' : Even (p + 1) := by
            apply Odd.add_odd hp.1 (by norm_num)
          rw [even_iff_two_dvd] at hp'
          obtain ⟨d, hd⟩ := hp'
          rw [hd] at h₀ ⊢
          rw [Nat.mul_comm, Nat.mul_div_cancel _ (by norm_num)]
          linarith only [h₀]
          -- Verify that k ≥ 2m.
          qify
          rw [<-sq_le_sq₀ (by positivity) (by positivity)]
          linarith [show (p : ℚ) ^ 2 ≥ 0 by positivity]
        . -- We have c = 2 and d = 1, and hence p² = p³, a contradiction.
          rw [h₄, h₅] at h₃
          norm_num at h₃
          symm at h₃
          rw [Nat.mul_eq_left] at h₃
          absurd hp.2
          rw [h₃]
          exact Nat.not_prime_one
          by_contra!
          simp at this
          rw [this] at hp
          norm_num at hp
    | inr h₀ =>
      -- We have 2n - p = -k, which is impossible because k > p.
      have : (k : ℚ) > p := by
        norm_cast at h₂ ⊢
        nlinarith
      qify at hn
      linarith
  . -- Now show that n = ((p + 1) / 2)² implies the condition.
    simp
    intro hn
    rw [hn]
    -- Note that p + 1 is even, so n = ((p + 1) / 2)².
    have hp' : Even (p + 1) := by
      apply Odd.add_odd hp.1 (by norm_num)
    rw [even_iff_two_dvd] at hp'
    obtain ⟨d, hd⟩ := hp'
    rw [hd] at hn ⊢
    rw [Nat.mul_comm, Nat.mul_div_cancel _ (by norm_num)] at hn ⊢
    refine ⟨?_, ?_⟩
    . -- Clearly 0 < d², otherwise a contradiction.
      by_contra!
      simp at this
      omega
    . -- We have √(n² - pn) = d(d - 1) = (p + 1) / 2 * (p - 1) / 2.
      use d * (d - 1)
      refine ⟨?_, ?_⟩
      . by_contra!
        simp at this
        replace hd : p < 2 := by
          omega
        absurd hd
        simp
        exact Nat.Prime.two_le hp.2
      . rw [Real.sqrt_eq_iff_eq_sq]
        rw [show (p : ℝ) = 2 * d - 1 by rify at hd; linarith]
        push_cast
        rw [mul_pow, show ((d - 1 : ℕ) : ℝ) ^ 2 = ((d - 1 : ℕ) : ℤ) ^ 2 by simp, <-Int.subNatNat_of_le (by by_contra!; simp at this; omega)]
        zify
        ring
        . -- Verify that 0 ≤ d² - dp.
          simp
          norm_cast
          nth_rw 2 [pow_two]
          apply Nat.mul_le_mul_left
          rw [<-@Nat.add_le_add_iff_right _ _ 1, hd]
          zify
          have := sq_nonneg (d - 1 : ℤ)
          linarith only [this]
        . -- Verify that 0 ≤ d(d - 1).
          simp
          norm_cast
          omega
