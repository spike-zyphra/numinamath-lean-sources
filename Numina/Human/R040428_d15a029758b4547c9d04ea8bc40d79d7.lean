import Mathlib

/-Let $T$ be a positive integer whose only digits are 0s and 1s. If $X = T \div 12$ and $X$ is an integer, what is the smallest possible value of $X$?-/
theorem number_theory_16235 :
    IsLeast {x | (∃T > 0, (∀a ∈ (Nat.digits 10 T), a = 1 ∨ a = 0) ∧ 12 ∣ T ∧ x = T / 12) } 925 := by
  -- First, we show that 925 is in the set. This means there exists some T such that T is divisible by 12, consists of only 0s and 1s, and T / 12 = 925.
  have _925_in_set: 925 ∈ {x | ∃ T > 0, (∀ a ∈ (Nat.digits 10 T), a = 1 ∨ a = 0) ∧ 12 ∣ T ∧ x = T / 12} := by
    simp
    -- We claim 11100 satisfies these conditions: 11100 is positive, its digits are only 1s and 0s, it is divisible by 12 and 11100 / 12 = 925.
    use 11100
    simp
    norm_num
  use _925_in_set
  -- Now, we show that 925 is the smallest value in the set.
  apply (le_csInf_iff' (Set.nonempty_of_mem _925_in_set)).mp
  apply le_csInf (Set.nonempty_of_mem _925_in_set)
  simp
  -- Suppose there exists some T, x which satisfy the set conditions.
  intro x T hT₀ hT₁ hT₂ hx
  -- Since 12 ∣ T, there exists some integer k such that T = 12k
  rcases hT₂ with ⟨k, hk⟩
  rw [hk] at hx
  -- So we have x = T / 12 = 12k / 12 = k
  have hxk : x = k := by
    rw [hx]
    apply Eq.symm (Nat.eq_div_of_mul_eq_left (by norm_num) (by linarith))

  -- Since 12 | T, we have 3 | T.
  have _3_dvd_T : 3 ∣ T := by
    rw [hk]
    apply (Nat.Prime.dvd_mul (by norm_num)).mpr
    apply Or.inl (by norm_num)
  -- Since 12 | T, we also have 4 | T.
  have _4_dvd_T : 4 ∣ T := by
    rw [hk, show 12 = 4 * 3 by linarith, mul_assoc]
    apply Nat.dvd_mul_right

  -- We know that 4 | T, so T must end in 00, 04, 08, 12, 16, ..., 92, 96. Since T can only contain 0 and 1, we can conclude that T must end in 00. Thus, 100 divides T.
  have _100_dvd_100 : 100 ∣ T := by
    -- apply dvd_iff_exists_eq_mul_right.mpr
    obtain ⟨r, hr⟩ := show ∃r, r = T % 100 by simp
    -- r is T mod 100, so r must only have digits 0 and 1.
    have hb : ∀b ∈ (Nat.digits 10 r), b = 1 ∨ b = 0 := by
      intro b hb
      by_cases hr': r = 0
      . have : (Nat.digits 10 r) = [] := by
          rw [hr']
          simp
        rw [this] at hb
        simp at hb
      by_cases h: T < 100
      . rw [show r = T by omega] at hb
        exact hT₁ b hb
      simp at h
      have : b ∈ (Nat.digits 10 T) := by
        have : 3 ≤ ((Nat.digits 10 T)).length := by
          rw [Nat.digits_len _ _ (by norm_num) (by linarith)]
          simp
          exact Nat.le_log_of_pow_le (by norm_num) h
        rw [Nat.digits_eq_cons_digits_div (by norm_num) hr'] at hb
        rw [Nat.digits_eq_cons_digits_div (by norm_num) (by linarith)]
        simp at hb
        simp
        obtain (hb | hb) := hb
        . -- b = r % 10
          apply Or.inl
          have : T % 10 = r % 10 := by omega
          rw [this]
          exact hb
        -- b ∈ (Nat.digits 10 (T / 10))
        apply Or.inr
        by_cases hr': r < 10
        . have : r / 10 = 0 := by exact Nat.div_eq_of_lt hr'
          rw [this] at hb
          simp at hb
        rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)] at hb
        rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)]
        simp at hb hr'
        simp
        obtain (hb | hb) := hb
        . -- b = r % 10
          apply Or.inl
          rw [hb]
          apply Nat.mod_eq_of_modEq ?_ (by omega)
          rw [←Nat.mod_mul_right_div_self, Nat.mod_mul_left_div_self, hr, ←Nat.mod_mul_right_div_self]
        have : r / 10 / 10 = 0 := by exact Nat.div_eq_of_lt (by omega)
        rw [this] at hb
        simp at hb
      exact hT₁ b this
    -- Since 4 divides T and 100, 4 must divide r
    have _4_dvd_r : 4 ∣ r := by
      rw [hr]
      apply (Nat.dvd_mod_iff (by norm_num)).mpr _4_dvd_T
    have hr': r < 100 := by omega
    by_cases hr'': r ≠ 0
    . rw [Nat.digits_eq_cons_digits_div (by norm_num) hr''] at hb
      simp at hb
      obtain ⟨hl, hr⟩ := hb
      obtain (hl | hl) := hl
      . -- r % 10 = 1, and 4 ∣ r, which is a contradiction
        omega
      . -- r % 10 = 0, and 4 ∣ r, so, r ∈ {20, 40, 60, 80}
        have : r = 20 ∨ r = 40 ∨ r = 60 ∨ r = 80  := by omega
        obtain (this | this | this | this) := this
        . -- r = 20
          rw [this] at hr
          simp at hr
        . -- r = 40
          rw [this] at hr
          simp at hr
        . -- r = 60
          rw [this] at hr
          simp at hr
        . -- r = 80
          rw [this] at hr
          simp at hr
    simp at hr''
    apply Nat.dvd_of_mod_eq_zero
    rw [hr.symm]
    exact hr''

  -- Since T has at least 3 digits, T >= 100.
  have hT₀ : 100 ≤ T := by omega
  rcases _100_dvd_100 with ⟨n, hn⟩
  have hn₁: 1 ≤ n := by omega

  -- Since 3 divides T, the sum of the digits of T must also be divisible by 3.
  have _3_dvd_sum : 3 ∣ (Nat.digits 10 T).sum := by exact (Nat.three_dvd_iff T).mp _3_dvd_T
  -- Since 100 divides T, the last two digits of T are zero. Thus, the digits of T are the digits of n, with two zeros appended.
  have hT₂: (Nat.digits 10 T) = 0 :: 0 :: Nat.digits 10 n := by
    rw [hn, Nat.digits_eq_cons_digits_div (by norm_num) (by omega)]
    rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)]
    simp
    use (by omega)
    use (by omega)
    omega
  rw [hT₂] at hT₁ _3_dvd_sum
  simp at hT₁ _3_dvd_sum
  -- Now, we need to show that n >= 111, we can do this by contradiction. If n < 111, then n must be 102, 105, or 108. But this is a contradiction to hT₁.
  have hn₂: 111 ≤ n := by
    rcases _3_dvd_sum with ⟨m, hm⟩
    by_cases h: m = 0
    . rw [h] at hm
      simp at hm
      absurd hm
      apply Nat.ne_zero_iff_zero_lt.mpr
      have (l : List ℕ) : 0 < l.sum ↔ ∃ x ∈ l, 0 < x := by
        induction l with
        | nil => simp
        | cons x xs ih =>
          simp [← ih]
      rw [this]

      use (Nat.digits 10 n).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr (by linarith))
      use (by apply List.getLast_mem)
      apply Nat.zero_lt_of_ne_zero
      apply Nat.getLast_digit_ne_zero
      linarith
    have : 3 ≤ (Nat.digits 10 n).sum := by omega
    have _100_le_n : 100 ≤ n := by
      have : 3 ≤ (Nat.digits 10 n).length := by
        apply le_trans
        exact this
        have (l : List ℕ) (h : ∀a ∈ l, a = 1 ∨ a = 0) :
             l.sum ≤ l.length := by
          induction l with
          | nil =>
            simp
          | cons a l ih =>
            simp at h
            obtain ⟨h₁, h₂⟩ := h
            specialize ih h₂
            simp
            obtain (h | h) := h₁
            . -- a = 1
              rw [h]
              linarith
            . -- a = 0
              rw [h]
              linarith
        exact this (Nat.digits 10 n) hT₁
      rw [Nat.digits_len _ _ (by linarith) (by linarith)] at this
      simp at this
      rw [show 100 = 10^2 by simp]
      apply Nat.pow_le_of_le_log (by linarith) this
    have : 3 ∣ n := by
      rw [hn] at _3_dvd_T
      apply Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) _3_dvd_T
    by_contra! hn_lt_111
    have : n = 102 ∨ n = 105 ∨ n = 108 := by omega
    obtain (this | this | this) := this
    . -- n = 102
      rw [this] at hT₁
      simp at hT₁
    . -- n = 105
      rw [this] at hT₁
      simp at hT₁
    . -- n = 108
      rw [this] at hT₁
      simp at hT₁
  omega
