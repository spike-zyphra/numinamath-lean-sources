import Mathlib

/- Trouver le plus petit entier positif qui ne s'écrit pas sous la forme $\frac{2^{a}-2^{b}}{2^{c}-2^{d}}$ pour $a, b, c, d \in \mathbb{N}$. -/
theorem number_theory_607606 : IsLeast {n : ℕ | n > 0 ∧ ¬∃ a b c d : ℕ, n = ((2 ^ a - 2 ^ b) / (2 ^ c - 2 ^ d) : ℚ)} 11 := by
  -- We can prove that from 1 to 10, all numbers can be expressed in the form given, and 11 cannot.
  have h0 : {n : ℕ | n > 0 ∧ ¬∃ a b c d : ℕ, n = ((2 ^ a - 2 ^ b) / (2 ^ c - 2 ^ d) : ℚ)} = Set.univ  \ {n : ℕ | ∃ a b c d : ℕ, n = ((2 ^ a - 2 ^ b) / (2 ^ c - 2 ^ d) : ℚ)} := by
    ext x; simp only [gt_iff_lt, not_exists, Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    specialize h 0 0 0 0
    simp only [pow_zero, sub_self, div_zero, Nat.cast_eq_zero] at h
    omega
  rw [h0]
  constructor
  · simp
    intro a b c d h₀
    have h₁ : (2 ^ c - 2 ^ d : ℚ) ≠ 0 := by
      intro hc
      simp [hc] at h₀
    rw [eq_div_iff h₁] at h₀
    wlog h₂ : b < a
    · push_neg at h₂
      by_cases h: a = b
      · rw [h] at h₀
        simp only [pow_zero, sub_self, div_zero, Nat.cast_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h₀
        exact h₁ h₀
      apply this h0 b a d c (by linarith) _ (by omega)
      intro h
      rw [sub_eq_zero] at h
      rw [h] at h₁
      norm_num at h₁
    have h₃ : d < c := by
      have : 0 < (2 ^ a - 2 ^ b : ℚ) := by
        rw [sub_pos]
        exact pow_lt_pow_right₀ rfl h₂
      contrapose! this
      rw [h₀.symm]
      simp only [@mul_nonpos_iff, Nat.ofNat_nonneg, tsub_le_iff_right, zero_add, true_and, sub_nonneg, (pow_le_pow_iff_right₀ (show 1 < (2 : ℚ) by norm_num)).mpr this, true_or]
    by_cases h₄ : d < b
    · set A := a - d with hA
      set B := b - d with hB
      set C := c - d with hC
      have h₅ : 11 * (2 ^ C - 1 : ℤ) = 2 ^ A - 2 ^ B := by
        suffices 11 * (2 ^ C - 1 : ℚ) = 2 ^ A - 2 ^ B by
          norm_cast at this
          norm_cast
        rw [show c = C + d by omega, show b = B + d by omega] at h₀
        rw [show a = A + d by omega, pow_add, pow_add, pow_add] at h₀
        rw [show (2 ^ C * 2 ^ d - 2 ^ d : ℚ) = 2 ^ d * (2 ^ C - 1) by ring_nf] at h₀
        rw [←sub_mul, mul_comm _ (2^d), mul_comm 11, mul_assoc, mul_comm _ 11] at h₀
        simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at h₀
        exact h₀
      have h₆ : Even (2 ^ A - 2 ^ B : ℤ) := by
        apply Even.sub
        apply Even.pow_of_ne_zero even_two (by omega)
        apply Even.pow_of_ne_zero even_two (by omega)
      apply Int.not_odd_iff_even.mpr h₆
      rw [h₅.symm]
      apply Odd.mul (by native_decide)
      apply Even.sub_odd _ odd_one
      apply Even.pow_of_ne_zero even_two (by omega)
    set A := a - b with hA
    set C := c - b with hC
    set D := d - b with hD
    have h₅ : 11 * (2 ^ C - 2 ^ D : ℤ) = 2^A - 1 := by
      suffices 11 * (2 ^ C - 2 ^ D : ℚ) = 2 ^ A - 1 by
        norm_cast at this
        norm_cast
      rw [show c = C + b by omega, show d = D + b by omega] at h₀
      rw [show a = A + b by omega, pow_add, pow_add, pow_add] at h₀
      rw [show (2 ^ A * 2 ^ b - 2 ^ b : ℚ) = 2 ^ b * (2 ^ A - 1) by ring_nf] at h₀
      rw [←sub_mul, mul_comm _ (2^b), mul_comm, mul_assoc] at h₀
      simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at h₀
      rw [h₀.symm]
      ring_nf
    have h₆ : D = 0 := by
      have h₆ : (11 * (2 ^ C - 2 ^ D) : ℤ) % 2 = 1 := by
        rw [h₅, Int.sub_emod]
        suffices (2^A : ℤ) % 2 = 0 by
          rw [this]
          norm_num
        rw [←@Int.even_iff]
        apply Even.pow_of_ne_zero even_two (by omega)
      have : (2 ^ C % 2 : ℤ) = 0 := by
        rw [←@Int.even_iff]
        apply Even.pow_of_ne_zero even_two (by omega)
      rw [Int.mul_emod, Int.sub_emod, this] at h₆
      norm_num at h₆
      contrapose! h₆
      norm_num
      exact dvd_pow_self 2 h₆
    rw [h₆] at h₅
    norm_num at h₅
    have h₇ : 10 + 2^A = 11 * 2^C := by linarith
    by_cases h₈ : 2 ≤ C
    · have h₉ : (10 + 2^A) % 4 = 0 := by
        rw [h₇]
        obtain ⟨k, hk⟩ := show ∃k, C = 2 + k by
          use C - 2
          omega
        rw [hk, pow_add, Nat.mul_mod, Nat.mul_mod]
        norm_num
      rw [Nat.add_mod] at h₉
      norm_num at h₉
      have h' : A = 1 := by
        by_cases h: 2 ≤ A
        · obtain ⟨k, hk⟩ := show ∃k, A = 2 + k by
            use A - 2
            omega
          rw [hk, pow_add, Nat.add_mod] at h₉
          norm_num at h₉
        by_cases h: A = 0
        · rw [h] at h₉
          norm_num at h₉
        omega
      rw [h'] at h₇
      norm_num at h₇
      absurd h₇
      apply ne_of_lt
      apply lt_of_lt_of_le (show 12 < 11 * 2 ^ 2 by norm_num)
      rw [mul_le_mul_left (by omega)]
      exact Nat.pow_le_pow_of_le (by linarith) h₈
    interval_cases C
    · -- C = 0
      omega
    · -- C = 1
      norm_num at h₅
      have h₉ : 2^A = 12 := by omega
      have : A < 4 := by
        rw [←pow_lt_pow_iff_right₀ (show 1 < 2 by norm_num), h₉]
        norm_num
      interval_cases A <;> norm_num at h₉
  · intro n hn
    by_contra!
    suffices ∀p, p ∈ Set.Icc 0 10 → ¬ p ∈ (Set.univ \ {n : ℕ | ∃ a b c d, n = ((2 ^ a - 2 ^ b) / (2 ^ c - 2 ^ d) : ℚ)}) by exact this n (by simp [show n ≤ 10 by omega]) hn
    rw [←Set.disjoint_left, disjoint_sdiff_iff_le (fun ⦃a⦄ a ↦ trivial) (fun ⦃a⦄ a ↦ trivial)]
    intro p
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
    intro hp
    interval_cases p
    · -- p = 0
      use 0, 0, 0, 0
      norm_num
    · -- p = 1
      use 1, 0, 1, 0
      norm_num
    · -- p = 2
      use 2, 1, 1, 0
      norm_num
    · -- p = 3
      use 2, 0, 1, 0
      norm_num
    · -- p = 4
      use 3, 2, 1, 0
      norm_num
    · -- p = 5
      use 4, 0, 2, 0
      norm_num
    · -- p = 6
      use 3, 1, 1, 0
      norm_num
    · -- p = 7
      use 3, 0, 1, 0
      norm_num
    · -- p = 8
      use 4, 3, 1, 0
      norm_num
    · -- p = 9
      use 6, 0, 3, 0
      norm_num
    · -- p = 10
      use 5, 1, 2, 0
      norm_num
