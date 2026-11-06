import Mathlib

/- Let $a$ and $b$ be distinct positive integers such that $3^{a}+2$ is divisible by $3^{b}+2$. Prove that $a>b^{2}$ 。 -/
theorem number_theory_605025 (a b : ℕ) (_ : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hdiv : 3^b + 2 ∣ 3^a + 2) : a > b^2 := by
  -- First we have a > b.
  have h₁ : a > b := by
    apply lt_of_le_of_ne _ hab.symm
    apply Nat.le_of_dvd (by positivity) at hdiv
    apply Nat.le_of_add_le_add_right at hdiv
    rw [Nat.pow_le_pow_iff_right (by norm_num)] at hdiv
    exact hdiv
  -- Let a = bq + r for q ≥ 1 and 0 ≤ r < b.
  let q := a / b
  let r := a % b
  have h₂ : 0 < q := by
    apply Nat.div_pos (le_of_lt h₁) hb
  have h₃ : a = b * q + r := by
    rw [Nat.div_add_mod a b]
  rw [h₃, add_comm _ r] at hdiv
  -- Consider the polynomial 3 ^ r * X ^ q + 2.
  let P : Polynomial ℤ := 3 ^ r * Polynomial.X ^ q + 2
  -- Consider the remainder when P is divided by X + 2 and substitute X = 3 ^ b.
  have h₄ : .X - .C (-2) ∣ P - .C (P.eval (-2)) := by
    apply Polynomial.X_sub_C_dvd_sub_C_eval
  simp [P] at h₄
  apply @Polynomial.eval_dvd _ _ _ _ (3 ^ b) at h₄
  simp [<-pow_mul, <-pow_add] at h₄
  -- We have 3 ^ b + 2 ∣ (-2) ^ q * 3 ^ r + 2.
  rw [show (3 : ℤ) ^ (r + b * q) - 3 ^ r * (-2) ^ q = 3 ^ (r + b * q) + 2 - ((-2) ^ q * 3 ^ r + 2) by ring] at h₄
  zify at hdiv
  rw [dvd_sub_right hdiv] at h₄
  -- Consider the parity of q.
  by_cases hq : Even q
  . -- Write (-2) ^ q * 3 ^ r + 2 = k (3 ^ b + 2) for some k ∈ ℕ.
    rw [Even.neg_pow hq] at h₄
    norm_cast at h₄
    rw [dvd_iff_exists_eq_mul_left] at h₄
    obtain ⟨k, h₄⟩ := h₄
    -- Show that 2 ≡ 2k (mod 3^r).
    have h₅ : 2 ≡ 2 * k [MOD 3 ^ r] := by
      calc
        _ ≡ 2 ^ q * 3 ^ r + 2 [MOD 3 ^ r] := by
          rw [Nat.modEq_iff_dvd' (by omega), Nat.add_sub_cancel]
          apply Nat.dvd_mul_left
        _ = k * (3 ^ b + 2) := by
          rw [<-h₄]
        _ ≡ 2 * k [MOD 3 ^ r] := by
          symm
          rw [mul_comm, Nat.modEq_iff_dvd' (by ring_nf; omega), mul_add, Nat.add_sub_cancel]
          calc
            _ ∣ 3 ^ b := by
              apply Nat.pow_dvd_pow
              simp [r]
              exact le_of_lt (Nat.mod_lt a (by omega))
            _ ∣ k * 3 ^ b := by
              apply Nat.dvd_mul_left
    -- Consider whether k > 1.
    by_cases hk : k = 1
    . -- Suppose that k = 1.
      simp [hk] at h₄
      -- We get 2 ∣ 3 ^ b, which is a contradiction.
      have h₅ : 2 ∣ 3 ^ b := by
        rw [<-h₄]
        calc
          2 ∣ 2 ^ q := by
            apply dvd_pow_self
            exact h₂.ne'
          _ ∣ 2 ^ q * 3 ^ r := by
            apply Nat.dvd_mul_right
      apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_two) at h₅
      norm_num at h₅
    . -- Suppose now that k > 1.
      have hk' : k ≠ 0 := by
        by_contra!
        simp [this] at h₄
      -- We have 3 ^ r ∣ k - 1.
      rw [Nat.modEq_iff_dvd' (by omega), show 2 = 2 * 1 by norm_num, <-Nat.mul_sub] at h₅
      rw [Nat.Coprime.dvd_mul_left (by simp; apply Odd.pow; use 1; rfl)] at h₅
      -- We have k ≥ 3 ^ r + 1.
      apply Nat.le_of_dvd (by omega) at h₅
      -- We have 2 ^ q * 3 ^ r + 2 > 3 ^ b * 3 ^ r + 2.
      have h₆ : 2 ^ q * 3 ^ r + 2 > 3 ^ b * 3 ^ r + 2 := by
        calc
          _ = k * (3 ^ b + 2) := h₄
          _ ≥ (3 ^ r + 1) * (3 ^ b + 2) := by
            apply Nat.mul_le_mul_right _ (by omega)
          _ > 3 ^ b * 3 ^ r + 2 := by
            ring_nf
            linarith [show 3 ^ r * 2 > 0 by positivity, show 3 ^ b > 0 by positivity]
      -- Therefore, 2 ^ q > 2 ^ b, and hence a > b ^ 2.
      have h₇ : 2 ^ b < 2 ^ q := by
        apply lt_of_add_lt_add_right at h₆
        rw [mul_lt_mul_right (by positivity)] at h₆
        calc
          2 ^ b < 3 ^ b := by
            rw [Nat.pow_lt_pow_iff_left (by positivity)]
            norm_num
          _ < 2 ^ q := h₆
      rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₇
      calc
        _ = b * q + r := h₃
        _ ≥ b * q := by
          omega
        _ > b * b := by
          apply Nat.mul_lt_mul_of_pos_left h₇ hb
        _ = b ^ 2 := by
          ring
  . -- Now we consider the case when q is odd.
    simp at hq
    rw [Odd.neg_pow hq] at h₄
    rw [<-dvd_neg, neg_add, <-sub_eq_add_neg] at h₄
    simp at h₄
    -- Show that 2 ^ q * 3 ^ r ≥ 2.
    have h₅ : 2 ^ q * 3 ^ r ≥ 2 := by
      calc
        2 ^ q * 3 ^ r ≥ 2 ^ q * 1 := by
          apply Nat.mul_le_mul_left
          apply Nat.one_le_pow _ _ (by norm_num)
        _ = 2 ^ q := by
          ring
        _ ≥ 2 := by
          apply Nat.le_self_pow h₂.ne'
    norm_cast at h₄
    -- Write 2 ^ q * 3 ^ r - 2 = k (3 ^ b + 2) for some k ∈ ℕ.
    rw [dvd_iff_exists_eq_mul_left] at h₄
    obtain ⟨k, h₄⟩ := h₄
    apply Nat.eq_add_of_sub_eq h₅ at h₄
    -- Show that 3 ^ r ∣ 2(k + 1).
    have h₆ : 3 ^ r ∣ 2 * (k + 1) := by
      rw [show k * (3 ^ b + 2) + 2 = 2 * (k + 1) + k * 3 ^ b by ring] at h₄
      have : 3 ^ r ∣ k * 3 ^ b := by
        calc
          3 ^ r ∣ 3 ^ b := by
            apply Nat.pow_dvd_pow
            simp [r]
            exact le_of_lt (Nat.mod_lt a (by omega))
          _ ∣ k * 3 ^ b := by
            apply Nat.dvd_mul_left
      rw [<-Nat.dvd_add_left this, <-h₄]
      apply Nat.dvd_mul_left
    -- Show that 3 ^ r ∣ k + 1.
    rw [Nat.Coprime.dvd_mul_left (by simp; apply Odd.pow; use 1; rfl)] at h₆
    -- Show that k + 1 ≥ 3 ^ r.
    apply Nat.le_of_dvd (by omega) at h₆
    by_cases hr : r = 0
    . -- Suppose r = 0.
      simp [hr] at h₄ hdiv h₃
      by_cases h₇ : k = 0 ∨ q = 1
      . rcases h₇ with (h₇ | h₇)
        -- Suppose that k = 0.
        simp [h₇] at h₄
        nth_rw 2 [show 2 = 2 ^ 1 by norm_num] at h₄
        -- We get q = 1.
        apply Nat.pow_right_injective (by norm_num) at h₄
        -- In either case, we get a = b, contradicting to our assumption that a and b are distinct.
        all_goals
          absurd hab
          simp [h₇, h₄, h₃]
      . -- Suppose that k > 0 and q > 1.
        -- We have 2 ^ q > 3 ^ b > 2 ^ b.
        have h₇ : 2 ^ q > 2 ^ b := by
          calc
            _ > 3 ^ b := by
              rw [h₄]
              nlinarith [show 1 ≤ k by omega, show 0 < 3 ^ b by positivity]
            _ > 2 ^ b := by
              rw [gt_iff_lt, Nat.pow_lt_pow_iff_left hb.ne']
              norm_num
        rw [gt_iff_lt, Nat.pow_lt_pow_iff_right (by norm_num)] at h₇
        calc
          _ = b * q := by
            omega
          _ > b * b := by
            apply Nat.mul_lt_mul_of_pos_left h₇ hb
          _ = b ^ 2 := by
            ring
    . -- Suppose that r > 0.
      have h₇ : 2 ^ (q + 1) * 3 ^ r > 3 ^ b * 3 ^ r := by
        calc
          _ = (k * (3 ^ b + 2) + 2) * 2 := by
            rw [<-h₄, pow_add]
            ring
          _ > (3 ^ r - 1) * (3 ^ b + 2) * 2 := by
            rw [gt_iff_lt, Nat.mul_lt_mul_right (by norm_num)]
            calc
              _ ≤ k * (3 ^ b + 2) := by
                apply Nat.mul_le_mul_right
                omega
              _ < k * (3 ^ b + 2) + 2 := by
                omega
          _ ≥ 3 ^ b * 3 ^ r := by
            rw [mul_comm (3 ^ r - 1), mul_assoc]
            apply Nat.mul_le_mul
            . omega
            . have : 3 ^ 1 ≤ 3 ^ r := by
                rw [Nat.pow_le_pow_iff_right (by norm_num)]
                omega
              omega
      -- We have 2 ^ (q + 1) > 3 ^ b.
      replace h₇ : 2 ^ (q + 1) > 3 ^ b := by
        apply lt_of_mul_lt_mul_right h₇
        positivity
      have h₈ : 2 ^ (q + 1) > 2 ^ b := by
        calc
          2 ^ (q + 1) > 3 ^ b := h₇
          _ > 2 ^ b := by
            rw [gt_iff_lt, Nat.pow_lt_pow_iff_left hb.ne']
            norm_num
      rw [gt_iff_lt, Nat.pow_lt_pow_iff_right (by norm_num)] at h₈
      -- We have q ≥ b.
      replace h₈ : q ≥ b := by
        omega
      by_cases h₉ : q = b
      . -- Suppose that q = b.
        simp [h₉] at h₃ h₇
        by_cases h₁₁ : b = 1
        . -- Suppose that b = 1, then a > b² is trivial.
          simp_all
        . -- Suppose that b > 1, then we derive a contradiction from 3 ^ b < 2 ^ (b + 1).
          have h₁₀ (n : ℕ) : n ≥ 2 → 2 ^ (n + 1) ≤ 3 ^ n := by
            intro hn'
            apply Nat.exists_eq_add_of_le at hn'
            obtain ⟨n', hn'⟩ := hn'
            rw [hn']
            clear n hn'
            -- We prove this by induction on n' = n - 2.
            induction n' with
            | zero => simp
            | succ n' h' =>
              rw [pow_add, <-add_assoc, pow_add 3]
              apply mul_le_mul
              . exact h'
              . norm_num
              . norm_num
              . positivity
          linarith only [h₇, h₁₀ b (by omega)]
      . -- Suppose that q > b.
        calc
          _ = b * q + r := h₃
          _ ≥ b * q := by
            omega
          _ > b * b := by
            apply Nat.mul_lt_mul_of_pos_left (show q > b by omega) hb
          _ = b ^ 2 := by
            ring
