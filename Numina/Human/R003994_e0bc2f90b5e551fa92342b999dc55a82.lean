import Mathlib

/- 5. Let $n$ be an arbitrary number written with 2000 digits and divisible by 9. Let the sum of the digits of the number $n$ be denoted by $a$, the sum of the digits of $a$ be denoted by $b$, and the sum of the digits of $b$ be denoted by $c$. Determine the number $c$. -/
theorem number_theory_228146 (n : ℕ) (h₀ : (Nat.digits 10 n).length = 2000)
    (h₁ : 9 ∣ n) (a b c : ℕ) (ha : a = (Nat.digits 10 n).sum)
    (hb : b = (Nat.digits 10 a).sum) (hc : c = (Nat.digits 10 b).sum) :
    c = 9 := by
  -- Prove that every digit $d$ in Nat.digits $10$ $m$ satisfies $d ≤ 9$.
  have h_digits_bound : ∀ m : ℕ, ∀ d ∈ Nat.digits 10 m, d ≤ 9 := by
    intros m d hd
    apply Nat.le_of_lt_succ
    apply Nat.digits_lt_base
    norm_num
    exact hd
  -- Prove that $a$ is the sum of digits of $n$, divisible by $9$, and $a ≤ 18000$.
  have h_a_div_9 : 9 ∣ a := by
    rw [ha]
    exact (Nat.nine_dvd_iff n).mp h₁
  have h_a_le_18000 : a ≤ 18000 := by
    rw [ha]
    -- Each digit $d$ ∈ Nat.digits $10$ $n$ satisfies $d ≤ 9$.
    have : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by
      apply List.sum_le_card_nsmul
      exact h_digits_bound n
    rw [h₀] at this
    linarith

  -- Prove that $b$ is the sum of digits of $a$, divisible by $9$, and $b ≤ 45$.
  have h_b_div_9 : 9 ∣ b := by
    rw [hb]
    exact (Nat.nine_dvd_iff a).mp h_a_div_9
  have h_b_le_45 : b ≤ 45 := by
    rw [hb]
    have : (Nat.digits 10 a).length ≤ 5 := by
        have : (Nat.digits 10 18000).length = 5 := by norm_num
        rw [← this]
        apply Nat.le_digits_len_le 10 a 18000
        linarith
    have : (Nat.digits 10 a).sum ≤ (Nat.digits 10 a).length * 9 := by
        apply List.sum_le_card_nsmul
        exact h_digits_bound a
    linarith

  -- Prove that $c$ is the sum of digits of $b$, divisible by $9$, and $c ≤ 9$, hence $c = 9$.
  have h_c_div_9 : 9 ∣ c := by
    rw [hc]
    exact (Nat.nine_dvd_iff b).mp h_b_div_9
  have h_c_le_9 : c ≤ 9 := by
    rw [hc]
    have : b ≤ 45 := h_b_le_45
    have h_b_len: (Nat.digits 10 b).length ≤ 2 := by
      have : (Nat.digits 10 45).length = 2 := by norm_num
      rw [← this]
      apply Nat.le_digits_len_le 10 b 45
      linarith
    have : (Nat.digits 10 b).sum ≤ 13 := by
      cases le_or_lt b 9 with
      | inl h_b_le_9 =>
        -- $b ≤ 9$, $b$ is a single digit, $c = b ≤ 9$.
        calc
          (Nat.digits 10 b).sum ≤ b := by
            apply Nat.digit_sum_le
          _ ≤ 9 := by assumption
          _ ≤ 13 := by norm_num
      | inr h_b_gt_9 =>
        -- $9 < b ≤ 45$, $b$ is a two-digit number, tens $digit ≤ 4$, units $digit ≤ 9$.
        have h1: b ≠ 0 := by linarith
        have h2: (Nat.digits 10 b) = [b % 10] ++ Nat.digits 10 (b / 10) := by
          apply Nat.digits_eq_cons_digits_div
          norm_num
          exact h1
        have h_ne_zero: b / 10 ≠ 0 := by omega
        have : b / 10 < 10 := by omega
        have h3 : Nat.digits 10 (b / 10) = [b / 10] := by
          apply Nat.digits_of_lt
          · exact h_ne_zero
          · exact this
        have h4 : (Nat.digits 10 b) = [b % 10, b / 10] := by
          rw [h2, h3]
          simp
        have : b / 10 ≤ 4 := by omega
        have : b % 10 ≤ 9 := by omega
        calc
          (Nat.digits 10 b).sum = (b % 10) + (b / 10) := by
            rw [h4]
            simp [List.sum]
          _ ≤ 9 + 4 := by linarith
          _ = 13 := by norm_num
    omega

  -- Prove $0 < c$.
  have h_c_gt_zero: 0 < c := by
    -- Prove $(Nat.digits 10 x).sum = 0 → x = 0$.
    have sum_zero_imp_zero : ∀ x : ℕ, (Nat.digits 10 x).sum = 0 → x = 0 := by
      intro x h_sum
      have : ∀ y ∈ Nat.digits 10 x, y = 0 := by
        apply List.sum_eq_zero_iff.mp
        exact h_sum
      have : Nat.digits 10 x = List.replicate (Nat.digits 10 x).length 0 := by
        apply List.eq_replicate_iff.mpr
        constructor
        · rfl
        · exact this
      have : Nat.ofDigits 10 (Nat.digits 10 x) = 0 := by
        rw [this]
        induction (Nat.digits 10 x).length with
        | zero => simp
        | succ m ih => simp [List.replicate, Nat.ofDigits]; rw [ih]
      rw [Nat.ofDigits_digits] at this
      exact this
    -- Prove $a > 0$.
    have : a > 0 := by
      rw [ha]
      by_contra h_a_npos
      have : a = 0 := by linarith
      have : n = 0 := by
        apply sum_zero_imp_zero
        rw [← ha, this]
      rw [this] at h₀
      simp [Nat.digits] at h₀
    -- Prove $b > 0$.
    have : b > 0 := by
      rw [hb]
      by_contra h_b_npos
      have : b = 0 := by linarith
      have : a = 0 := by
        apply sum_zero_imp_zero
        rw [← hb, this]
      linarith
    -- Prove $c > 0$.
    rw [hc]
    by_contra h_c_npos
    have : c = 0 := by linarith
    have : b = 0 := by
      apply sum_zero_imp_zero
      rw [← hc, this]
    linarith

  -- Combine the above conclusions to deduce $c = 9$.
  have h_c_eq_9 : c = 9 := by omega
  exact h_c_eq_9
