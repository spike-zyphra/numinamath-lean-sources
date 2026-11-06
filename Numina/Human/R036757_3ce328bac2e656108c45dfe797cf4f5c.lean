import Mathlib

/- Trouver tous les entiers $m \geqslant 1$ et $n \geqslant 1$ tels que $\frac{5^{m}+2^{n+1}}{5^{m}-2^{n+1}}$ soit le carré d'un entier. -/
theorem number_theory_605132 :
    {(m, n) : ℕ × ℕ | 1 ≤ m ∧ 1 ≤ n ∧ ∃ k : ℤ, k ^ 2 = (5 ^ m + 2 ^ (n + 1) : ℚ) / (5 ^ m - 2 ^ (n + 1) : ℚ)} = {(1, 1)} := by
  -- Break the goal into two parts.
  ext ⟨m, n⟩
  simp
  apply Iff.intro
  . -- First show that if (m, n) satisfies the condition, then (m, n) = (1, 1).
    rintro ⟨hm, hn, k', h₁⟩
    -- Make sure that k ≥ 0 by choosing the non-negative one.
    let k := |k'|
    rw [show (k' ^ 2 : ℚ) = k ^ 2 by simp [k]] at h₁
    -- Show that 5 ^ m - 2 ^ (n + 1) ≠ 0, because 5 and 2 are prime numbers.
    have h₂ : (5 ^ m - 2 ^ (n + 1) : ℤ) ≠ 0 := by
      by_contra!
      apply eq_of_sub_eq_zero at this
      norm_cast at this
      apply Nat.exists_eq_add_of_le' at hm
      obtain ⟨m', hm⟩ := hm
      rw [hm] at this
      apply Nat.Prime.pow_inj (Nat.prime_five) (Nat.prime_two) at this
      tauto
    qify at h₂
    field_simp at h₁
    -- Show that 5 ^ m - 2 ^ (n + 1) divides 2 ^ (n + 2).
    have h₃ : (5 ^ m - 2 ^ (n + 1) : ℤ) ∣ 2 ^ (n + 2) := by
      rw [show (2 ^ (n + 2) : ℤ) = (5 ^ m + 2 ^ (n + 1)) - (5 ^ m - 2 ^ (n + 1)) by ring]
      apply Int.dvd_sub
      . -- Use the above result that k²(5 ^ m - 2 ^ (n + 1)) = (5 ^ m + 2 ^ (n + 1)).
        rw [dvd_iff_exists_eq_mul_left]
        use k ^ 2
        qify
        exact h₁.symm
      . rfl
    -- Note that 5 ^ m - 2 ^ (n + 1) > 0 is a natural number, otherwise k²(5 ^ m - 2 ^ (n + 1)) < 0 is impossible.
    let c := (5 ^ m - 2 ^ (n + 1) : ℤ).natAbs
    have h₄ : c = (5 ^ m - 2 ^ (n + 1) : ℤ) := by
      simp [c]
      rw [<-Int.sub_nonneg]
      by_contra!
      -- Assume on the contrary that 5 ^ m - 2 ^ (n + 1) < 0, then 5 ^ m + 2 ^ (n + 1) = k²(5 ^ m - 2 ^ (n + 1)) < 0, a contradiction.
      qify at this
      nlinarith [sq_nonneg (k : ℚ), show 0 < (5 ^ m + 2 ^ (n + 1) : ℚ) by positivity]
    -- Since c = 5 ^ m - 2 ^ (n + 1) divides a power of 2, it is a power of 2.
    rw [<-h₄] at h₃
    norm_cast at h₃
    rw [Nat.dvd_prime_pow (Nat.prime_two)] at h₃
    obtain ⟨n', h₃, h₅⟩ := h₃
    -- Now 5 ^ m - 2 ^ (n + 1) = 2 ^ n', by comparing parity, we conclude that n' = 0.
    have h₆ : n' = 0 := by
      by_contra! h₆
      replace h₆ : 1 ≤ n' := by
        omega
      apply Nat.exists_eq_add_of_le' at h₆
      obtain ⟨n'', h₆⟩ := h₆
      zify at h₅
      rw [h₆, h₄] at h₅
      apply eq_add_of_sub_eq at h₅
      norm_cast at h₅
      -- Note that 5 ^ m is odd, but 2 ^ (n'' + 1) + 2 ^ (n + 1) clear is not.
      have : Odd (5 ^ m) := by
        apply Odd.pow (by use 2; rfl)
      rw [h₅] at this
      absurd this
      simp [pow_add]
      rw [<-add_mul]
      simp
    -- Now 5 ^ m - 2 ^ (n + 1) = 1.
    simp [h₅, h₆] at h₄
    qify at h₄
    simp [<-h₄] at h₁
    symm at h₄
    apply eq_add_of_sub_eq at h₄
    rw [h₄] at h₁
    -- We have (k - 1)(k + 1) = 2 ^ (n + 2).
    replace h₁ : (k - 1) * (k + 1) = 2 ^ (n + 2) := by
      qify
      ring_nf at h₁ ⊢
      linarith
    -- Now both k - 1 and k + 1 divides 2 ^ (n + 2).
    have h₇ : k - 1 ∣ 2 ^ (n + 2) := by
      rw [<-h₁]
      apply Int.dvd_mul_right
    have h₈ : k + 1 ∣ 2 ^ (n + 2) := by
      rw [<-h₁]
      apply Int.dvd_mul_left
    -- We show that both k - 1 and k + 1 are powers of 2.
    rw [dvd_prime_pow (Int.prime_two)] at h₇ h₈
    simp [Associated] at h₇ h₈
    obtain ⟨c, h₇, c', h₉⟩ := h₇
    obtain ⟨d, h₈, d', h₁₀⟩ := h₈
    replace h₉ := congr_arg (·.natAbs) h₉
    replace h₁₀ := congr_arg (·.natAbs) h₁₀
    simp [Int.natAbs_mul, Int.units_natAbs] at h₉ h₁₀
    zify at h₉ h₁₀
    -- Note that k > 0.
    have h₁₁ : k > 0 := by
      apply lt_of_le_of_ne
      . simp [k]
      . by_contra!
        simp [<-this] at h₁
        linarith only [h₁, show 0 < 2 ^ (n + 2) by positivity]
    -- We have k - 1 = 2 ^ c and k + 1 = 2 ^ d.
    rw [abs_of_nonneg (show 0 ≤ k - 1 by omega), abs_of_nonneg (show 0 ≤ (2 ^ c : ℤ) by positivity)] at h₉
    rw [abs_of_nonneg (show 0 ≤ k + 1 by positivity), abs_of_nonneg (show 0 ≤ (2 ^ d : ℤ) by positivity)] at h₁₀
    -- We have c < d.
    have h₁₂ : 2 ^ c < 2 ^ d := by
      zify
      rw [<-h₉, <-h₁₀]
      omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₁₂
    -- We have 2 ^ c * (2 ^ (d - c) - 1) = 2.
    have h₁₃ : 2 ^ c * (2 ^ (d - c) - 1 : ℤ) = 2 := by
      rw [mul_sub, <-pow_add, Nat.add_sub_cancel', <-h₉, <-h₁₀]
      omega
      exact le_of_lt h₁₂
    -- Now c = 0 or 1.
    have h₁₄ : 2 ^ c ≤ 2 ^ 1 := by
      apply Nat.le_of_dvd (by norm_num)
      zify
      simp
      nth_rw 3 [<-h₁₃]
      apply Int.dvd_mul_right
    rw [Nat.pow_le_pow_iff_right (by norm_num)] at h₁₄
    interval_cases c
    . -- Suppose c = 0, then 2 ^ d - 1 = 2, no solution.
      simp at h₁₃
      apply eq_add_of_sub_eq at h₁₃
      -- We have 2 < 2 ^ d < 4, so 1 < d < 2, contradiction.
      have h₁₅ : 2 ^ 1 < 2 ^ d ∧ 2 ^ d < 2 ^ 2 := by
        zify
        rw [h₁₃]
        norm_num
      iterate 2 rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₁₅
      omega
    . -- Suppose c = 1, then 2 ^ (d - 1) - 1 = 1.
      simp at h₁₃
      replace h₁₃ : 2 ^ (d - 1) = 2 ^ 1 := by
        linarith
      apply Nat.pow_right_injective (by norm_num) at h₁₃
      -- We get m = n = 1.
      rw [h₉, h₁₀, show d = 2 by omega] at h₁
      -- We have 2 ^ (n + 2) = 2 ^ 3, so n = 1.
      replace h₁ : 2 ^ (n + 2) = 2 ^ 3 := by
        linarith
      apply Nat.pow_right_injective (by norm_num) at h₁
      replace h₁ : n = 1 := by
        omega
      -- We have 5 ^ m = 5, so m = 1.
      norm_num [h₁] at h₄
      norm_cast at h₄
      rw [Nat.pow_eq_self_iff (by norm_num)] at h₄
      tauto
  . -- Verify that m = n = 1 satisfies the condition
    rintro ⟨hm, hn⟩
    norm_num [hm, hn]
    use 3
    norm_num