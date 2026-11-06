import Mathlib

theorem number_theory_5849 : {(a, b) : ℕ×ℕ | 1 ≤ a ∧ 1 ≤ b ∧ a ^ (b ^ 2) = b^a} = {(1, 1), (16, 2), (27, 3)} := by
  ext ⟨a, b⟩
  constructor <;> simp
  · -- 1 ≤ a → 1 ≤ b → a ^ b ^ 2 = b ^ a → a = 1 ∧ b = 1 ∨ a = 16 ∧ b = 2 ∨ a = 27 ∧ b = 3
    intro ha hb hab
    by_cases h₁: a = b
    · -- if a = b, the solution is a = 1 ∧ b = 1
      apply Or.inl
      rw [h₁] at hab ⊢
      simp
      rw [show b ^ b ^ 2 = (b ^ b) ^ b by ring_nf] at hab
      have : (b ^ b) ^ (b - 1) = 1 := by
        nth_rewrite 3 [show b = b - 1 + 1 by omega] at hab
        rw [Nat.pow_add_one] at hab
        nth_rewrite 3 [←Nat.mul_one (b ^ b)] at hab
        rw [Nat.mul_comm, Nat.mul_left_cancel_iff] at hab
        exact hab
        exact Nat.pos_pow_of_pos b hb
      by_cases h₂: b - 1 = 0
      · omega
      rw [pow_eq_one_iff h₂, pow_eq_one_iff (by omega)] at this
      exact this
    apply Or.inr
    have ha₂ : 2 ≤ a := by
      by_contra! h₂
      rw [show a = 1 by omega] at hab h₁
      simp at hab
      omega
    have hb₂ : 2 ≤ b := by
      by_contra! h₂
      rw [show b = 1 by omega] at hab h₁
      simp at hab
      omega
    by_cases hb₃: b = 2
    · rw [hb₃] at hab ⊢
      simp at hab ⊢
      -- we need to solve the equation a ^ 4 = 2 ^ a. First we show that a ^ 4 < 2 ^ a for a > 16
      have : ∀ x, (x + 17)^4 < 2^(x + 17) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          apply lt_trans (show (n + 1 + 17) ^ 4 < 2 * (n + 17) ^ 4 by ring_nf; omega)
          rw [show 2 ^ (n + 1 + 17) = 2 * 2 ^ (n + 17) by ring_nf]
          simp
          exact ih
      have ha₃ : a ≤ 16 := by
        by_contra! h₃
        specialize this (a - 17)
        rw [show a - 17 + 17 = a by omega] at this
        linarith
      interval_cases a <;>
        norm_num at hab ⊢
    have hb₂ : 3 ≤ b := by omega
    apply Or.inr
    by_cases hb₃: b = 3
    · rw [hb₃] at hab ⊢
      simp at hab ⊢
      -- we need to solve the equation a ^ 9 = 3 ^ a. First we show that a ^ 9 < 3 ^ a for a > 27
      have : ∀ x, (x + 28)^9 < 3^(x + 28) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          apply lt_trans (show (n + 1 + 28) ^ 9 < 3 * (n + 28) ^ 9 by ring_nf; omega)
          rw [show 3 ^ (n + 1 + 28) = 3 * 3 ^ (n + 28) by ring_nf]
          simp
          exact ih
      have ha₃ : a ≤ 27 := by
        by_contra! h₃
        specialize this (a - 28)
        rw [show a - 28 + 28 = a by omega] at this
        linarith
      interval_cases a <;>
        norm_num at hab ⊢
    have hb₂ : 4 ≤ b := by omega
    obtain ⟨k, hk₁, hk₂⟩ := show ∃k, k = b^(k - 2) ∧ k > 2 by
      have h₂ : a > b := by
        suffices b^a > b^b by exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
        rw [←hab]
        have : 2^(b^2) > b^b := by
          rw [pow_two, Nat.pow_mul]
          exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
        apply lt_of_lt_of_le this
        exact Nat.pow_le_pow_of_le_left ha₂ (b ^ 2)
      have h₃ : a > b^2 := by
        suffices b^a > b^(b^2) by exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
        rw [←hab]
        exact Nat.pow_lt_pow_left h₂ (by simp; omega)
      have h₄ : a > 2 * b^2 := by
        suffices b^a > b^(2 * b^2) by exact (Nat.pow_lt_pow_iff_right (by omega)).mp this
        rw [←hab, Nat.pow_mul]
        exact Nat.pow_lt_pow_left h₃ (by simp; omega)
      have h₅ : ∀p, b^2 * a.factorization p = a * b.factorization p := by
        intro p
        suffices (a^b^2).factorization p = (b^a).factorization p by
          simp at this
          linarith
        exact congrFun (congrArg DFunLike.coe (congrArg Nat.factorization hab)) p
      obtain ⟨k, hk₁⟩ := show b^2 ∣ a by
        apply (Nat.factorization_prime_le_iff_dvd (by linarith [Nat.pos_pow_of_pos 2 hb]) (by omega)).mp
        intro p hp
        simp
        specialize h₅ p
        suffices 2 * b.factorization p ≤ (a : ℝ) * b.factorization p / b^2 by
          rw [←Nat.cast_mul, ←h₅] at this
          field_simp at this
          norm_cast at this
        rw [mul_comm (a : ℝ), ←mul_div, mul_comm]
        apply mul_le_mul_of_nonneg (Preorder.le_refl _) ?_ (Nat.cast_nonneg' (b.factorization p))
        apply div_nonneg (Nat.cast_nonneg' a) (sq_nonneg _)
        apply (le_div_iff₀' (sq_pos_of_pos (Nat.cast_pos'.mpr hb))).mpr
        norm_cast
        linarith
      use k
      split_ands
      · have h₆ : ∀p, a.factorization p = k * b.factorization p := by
          intro p
          specialize h₅ p
          rw [hk₁, mul_assoc, Nat.mul_left_cancel_iff (Nat.pos_pow_of_pos 2 hb), ←hk₁] at h₅
          exact h₅
        have h₇ : a = b^k := by
          rw [←Nat.factorization_prod_pow_eq_self (show a ≠ 0 by omega)]
          rw [←Nat.factorization_prod_pow_eq_self (pow_ne_zero k (by omega))]
          simp
          have : k • b.factorization = a.factorization := by
            ext p
            rw [h₆ p]
            norm_num
          rw [this]
        have : b^k = b^2 * b^(k - 2) := by
          have : k > 2 := by
            rw [hk₁, mul_comm] at h₄
            exact Nat.lt_of_mul_lt_mul_right h₄
          rw [←Nat.pow_add, show 2 + (k - 2) = k by omega]
        rw [h₇, this, Nat.mul_left_cancel_iff (Nat.pos_pow_of_pos 2 hb)] at hk₁
        exact hk₁.symm
      · rw [hk₁, mul_comm] at h₄
        exact Nat.lt_of_mul_lt_mul_right h₄
    have : ∀ x, x + 3 < 4 ^ (x + 1) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [Nat.pow_add_one]
        linarith
    specialize this (k - 3)
    rw [show k - 3 + 1 = k - 2 by omega, show k - 3 + 3 = k by omega] at this
    have hk₃ : k < b ^ (k - 2) := by
      apply lt_of_lt_of_le this
      exact Nat.pow_le_pow_of_le_left hb₂ (k - 2)
    linarith
  · -- a = 1 ∧ b = 1 ∨ a = 16 ∧ b = 2 ∨ a = 27 ∧ b = 3 → 1 ≤ a ∧ 1 ≤ b ∧ a ^ b ^ 2 = b ^ a
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      rw [ha, hb] <;>
      norm_num
