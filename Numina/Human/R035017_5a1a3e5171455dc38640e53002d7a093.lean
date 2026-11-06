import Mathlib

/- Trouver tous les entiers $\mathrm{m}, \mathrm{n} \geq 0$ tels que $n^{3}-3 n^{2}+n+2=5^{m}$. -/
theorem number_theory_607695 :
    {(m, n) : ℕ × ℕ | (n ^ 3 - 3 * n ^ 2 + n + 2 : ℤ) = 5 ^ m} = {(0, 1), (1, 3)} := by
  -- Break the goal into two parts.
  ext ⟨m, n⟩
  constructor
  . -- Show that the condition implies that (m, n) = (0, 1) or (1, 3).
    rintro h₀
    simp at h₀
    -- Factorize n³ - 3n² + n + 2 = (n - 2)(n² - n - 1).
    rw [show n ^ 3 - 3 * n ^ 2 + n + 2 = (n - 2) * (n ^ 2 - n - 1 : ℤ) by ring] at h₀
    -- Show that n ≠ 2.
    have h₁ : n ≠ 2 := by
      by_contra!
      simp [this] at h₀
      linarith [show 0 < 5 ^ m by positivity]
    rcases ne_iff_lt_or_gt.mp h₁ with (h₁ | h₁)
    . -- Consider the case n < 2.
      interval_cases n
      . -- If n = 0, then 5 ^ m = 2, impossible.
        simp at h₀
        have h₂ : 5 ^ 0 < 5 ^ m := by
          linarith
        have h₃ : 5 ^ m < 5 ^ 1 := by
          linarith
        rw [Nat.pow_lt_pow_iff_right (by omega)] at h₂ h₃
        linarith
      . -- If n = 1, we have m = 0, one of our solutions.
        simp at h₀
        norm_cast at h₀
        rw [show 1 = 5 ^ 0 by norm_num] at h₀
        apply Nat.pow_right_injective (by norm_num) at h₀
        tauto
    . -- Consider the case n > 2, so n - 2 and n² - n - 1 are both positive.
      have h₂ : (n - 2 : ℤ) > 0 := by
        linarith
      have h₃ : (n ^ 2 - n - 1 : ℤ) > 0 := by
        nlinarith
      replace h₀ := congr_arg (Int.natAbs ·) h₀
      simp [Int.natAbs_mul] at h₀
      rw [show ((5 : ℤ) ^ m).natAbs = 5 ^ m by norm_cast] at h₀
      -- Since n - 2 and n² - n - 1 multiples to be a power of 5, both of them are powers of 5.
      have h₄ : ∃ k ≤ m, (n - 2 : ℤ).natAbs = 5 ^ k := by
        rw [<-Nat.dvd_prime_pow Nat.prime_five, <-h₀]
        apply Nat.dvd_mul_right
      have h₅ : ∃ k ≤ m, (n ^ 2 - n - 1 : ℤ).natAbs = 5 ^ k := by
        rw [<-Nat.dvd_prime_pow Nat.prime_five, <-h₀]
        apply Nat.dvd_mul_left
      obtain ⟨k₀, h₄, h₆⟩ := h₄
      obtain ⟨k₁, h₅, h₇⟩ := h₅
      zify at h₆ h₇
      simp [abs_of_nonneg, le_of_lt h₂, le_of_lt h₃] at h₆ h₇
      -- Note that n - 2 ≤ n² - n - 1, so 5 ^ k₀ ≤ 5 ^ k₁.
      have h₈ : 5 ^ k₀ ≤ 5 ^ k₁ := by
        zify
        rw [<-h₆, <-h₇]
        -- This is basicaclly (n - 1)² ≥ 0.
        linarith only [sq_nonneg (n - 1 : ℤ)]
      rw [Nat.pow_le_pow_iff_right (by norm_num)] at h₈
      -- We have n - 2 ∣ n² - n - 1.
      have h₄ : (n - 2 : ℤ) ∣ (n ^ 2 - n - 1 : ℤ) := by
        rw [h₆, h₇]
        norm_cast
        apply Nat.pow_dvd_pow
        exact h₈
      -- However, note that n² - n - 1 = (n - 2)(n + 1) + 1.
      rw [show (n ^ 2 - n - 1 : ℤ) = (n - 2) * (n + 1) + 1 by ring, Int.dvd_add_right (by apply dvd_mul_right)] at h₄
      -- Now we have n - 2 ∣ 1.
      apply Int.eq_one_of_dvd_one (le_of_lt h₂) at h₄
      -- Thus n = 3, m = 1, corresponding to the other solution.
      replace h₄ : n = 3 := by
        zify
        linarith
      simp [h₄] at h₀
      nth_rw 1 [show 5 = 5 ^ 1 by norm_num] at h₀
      apply Nat.pow_right_injective (by norm_num) at h₀
      simp
      tauto
  . -- Check that m = 0, n = 1 and m = 1, n = 3 are indeed solutions.
    rintro (⟨m, n⟩ | ⟨m, n⟩)
    <;> norm_num