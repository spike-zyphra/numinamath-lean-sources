import Mathlib

/- 1. (BUL) Find all the three-digit numbers for which one obtains, when dividing the number by 11 , the sum of the squares of the digits of the initial number.-/
theorem other_24486 (n : ℕ) (hdigit : (Nat.digits 10 n).length = 3) (hdvd : 11 ∣ n)
    (hsum : ((Nat.digits 10 n).map (· ^ 2)).sum = n / 11) :
    n = 550 ∨ n = 803 := by
  rw [List.length_eq_three] at hdigit
  rcases hdigit with ⟨b, c, a, hdigit⟩
  -- Since $\overline{a c b}$ is a three-digit number, $a$ cannot be zero.
  have ha_nezero : a ≠ 0 := by
    have := @Nat.getLast_digit_ne_zero 10 n (by rw [← @Nat.digits_ne_nil_iff_ne_zero 10]; simp [hdigit])
    convert this
    simp [hdigit]
  -- Since $a,b,c$ are decimal digits, we have $a,b,c<10$.
  have ⟨ha, hb, hc⟩ : a < 10 ∧ b < 10 ∧ c < 10 := by
    split_ands
    all_goals
      apply Nat.digits_lt_base (m := n) (by norm_num)
      simp [hdigit]
  -- We can write three-digit number $n$ as $100a+10b+c$.
  have hn : n = 100 * a + 10 * c + b := by
    rw [← Nat.ofDigits_digits 10 n, hdigit]
    repeat rw [Nat.ofDigits]
    norm_cast
    ring
  -- Since the sum of the squares of the digits of the initial number equals $n / 11$,
  -- we have $a^2+b^2+c^2 = (100a+10b+c) / 11$.
  simp [hdigit] at hsum
  rw [hn] at hsum
  -- We use modular arithemetic to deduce that $11 | a+b-c$.
  have ten_mod11 : 10 ≡ -1 [ZMOD 11] := rfl
  have hundred_mod11 : 100 ≡ 1 [ZMOD 11] := rfl
  have abc_mod11 : 1 * a + (-1) * c + b ≡ 0 [ZMOD 11] := by
    zify at hdvd hn
    rw [← Int.modEq_zero_iff_dvd, hn] at hdvd
    have h1 := hundred_mod11.mul (Int.ModEq.refl a)
    have h2 := ten_mod11.mul (Int.ModEq.refl c)
    have h3 := Int.ModEq.refl (n := 11) b
    have := h1.add (h2.add h3)
    trans 100 * a + 10 * c + b
    . symm
      convert this using 1
      all_goals ring
    exact hdvd
  rw [Int.modEq_zero_iff_dvd] at abc_mod11
  -- Lemmas to check parity.
  have sq_even_of_even {n : ℕ} (hn : Even n) : Even (n ^ 2) := by
    rw [pow_two]
    exact Even.mul_right hn n
  have sq_odd_of_odd {n : ℕ} (hn : Odd n) : Odd (n ^ 2) := by
    rw [pow_two]
    exact Odd.mul hn hn
  have sq_even_of_even' {n : ℕ} (hn : Even (n : ℤ)) : Even (n ^ 2 : ℤ) := by
    rw [pow_two]
    exact Even.mul_right hn ↑n
  have sq_odd_of_odd' {n : ℕ} (hn : Odd (n : ℤ)) : Odd (n ^ 2 : ℤ) := by
    rw [pow_two]
    exact Odd.mul hn hn
  -- Since $a,b,c<10$, we must have $c=a+b$ or $c=a+b-11$.
  rcases abc_mod11 with ⟨k, hk⟩
  have : 0 ≤ k := by omega
  have : k ≤ 1 := by omega
  interval_cases h : k
  . -- Case (1): c=a+b.
    have : (c : ℤ) = a + b := by linear_combination -hk
    norm_cast at this
    rw [show 100 * a + 10 * c + b = 11 * (10 * a + b) by rw [this]; ring, this] at hsum
    -- We have $a^2+b^2+c^2=10a+b$.
    simp at hsum
    -- We can deduce that $b$ is even.
    have hbeven : Even b := by
      by_contra h
      rw [Nat.not_even_iff_odd] at h
      have : Odd (10 * a + b) := by
        apply Even.add_odd
        . apply Even.mul_right
          use 5
        exact h
      rcases Nat.even_or_odd a with ha | ha
      . have : ¬Odd (10 * a + b) := by
          rw [← hsum, Nat.not_odd_iff_even]
          apply Odd.add_odd
          . exact sq_odd_of_odd h
          apply Odd.add_even
          . apply sq_odd_of_odd
            exact Even.add_odd ha h
          exact sq_even_of_even ha
        contradiction
      have : ¬Odd (10 * a + b) := by
        rw [← hsum, Nat.not_odd_iff_even]
        apply Odd.add_odd
        . exact sq_odd_of_odd h
        apply Even.add_odd
        . apply sq_even_of_even
          exact Odd.add_odd ha h
        exact sq_odd_of_odd ha
      contradiction
    rw [Nat.even_iff] at hbeven
    rw [hn, this]
    -- Hence, $b$ can be 0,2,4,6,8.
    interval_cases b <;> norm_num at hbeven
    -- `hsum` is a quadratic equation of $a$.
    all_goals contrapose! hsum
    -- The only possibility is n=550 or n=803.
    any_goals interval_cases a <;> norm_num
    . norm_num at ha_nezero
    norm_num at hsum
  -- Case (2): c=a+b-11.
  have : (c : ℤ) = a + b - 11 := by linear_combination -hk
  zify at hsum
  rw [show 100 * (a : ℤ) + 10 * c + b = 11 * (10 * (a - 1) + b) by rw [this]; ring, this] at hsum
  -- We have $a^2+b^2+c^2=10(a-1)+b$.
  simp at hsum
  -- We can deduce that $b$ is odd.
  have hbodd : Odd b := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    replace h : Even (b : ℤ) := by
      rcases h with ⟨k, hk⟩
      use k
      assumption_mod_cast
    have : Even (10 * (a - 1) + (b : ℤ)) := by
      apply Even.add
      . apply Even.mul_right
        use 5
        norm_num
      exact h
    rcases Int.even_or_odd a with ha | ha
    . have : ¬Even (10 * (a - 1) + (b : ℤ)) := by
        rw [← hsum, Int.not_even_iff_odd]
        apply Even.add_odd
        . exact sq_even_of_even' h
        apply Odd.add_even
        . rw [Int.odd_pow]
          left
          apply Even.sub_odd
          . exact Even.add ha h
          use 5
          norm_num
        exact sq_even_of_even' ha
      contradiction
    have : ¬Even (10 * (a - 1) + (b : ℤ)) := by
      rw [← hsum, Int.not_even_iff_odd]
      apply Even.add_odd
      . exact sq_even_of_even' h
      apply Even.add_odd
      . rw [Int.even_pow]
        refine ⟨?_, by norm_num⟩
        apply Odd.sub_odd
        . exact Even.odd_add h ha
        use 5
        norm_num
      exact sq_odd_of_odd' ha
    contradiction
  rw [Nat.odd_iff] at hbodd
  rw [hn]
  zify
  rw [this]
  -- Hence, $b$ can be 1,3,5,7,9.
  interval_cases b <;> norm_num at hbodd
  -- `hsum` is a quadratic equation of $a$.
  all_goals contrapose! hsum
  -- The only possibility is n=550 or n=803.
  any_goals interval_cases a <;> norm_num
  . norm_num at this
    aesop
  norm_num at hsum
