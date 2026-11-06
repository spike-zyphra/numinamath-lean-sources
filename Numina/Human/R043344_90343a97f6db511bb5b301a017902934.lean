import Mathlib

/-Let the sequence $a_{i}$ be defined as $a_{i+1}=2^{a_{i}}$. Find the number of integers $1 \leq n \leq 1000$ such that if $a_{0}=n$, then 100 divides $a_{1000}-a_{1}$.-/
theorem number_theory_609582 :
  {n : ℕ | 1 ≤ n ∧ n ≤ 1000 ∧
    ∀ a : ℕ → ℕ, (∀ i, a (i + 1) = 2 ^ (a i)) → a 0 = n → (100 : ℤ) ∣ a 1000 - a 1
  }.ncard = 50 := by

  -- clearly all a i is positive
  have h_a_pos (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) : ∀ n ≥ 1, a n ≥ 1 := by
    intro n hn
    match n with
    | 0 => simp at hn
    | n + 1 => rw [ha n]; exact Nat.one_le_two_pow

  -- so from n = 2, a n is divisible by 2
  have h_a_even (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) : ∀ n ≥ 2, 2 ∣ a n := by
    intro n hn
    match n with
    | 0 | 1 => simp at hn
    | n + 1 + 1 =>
      rw [ha]
      refine dvd_pow ?_ ?_
      norm_num
      have := h_a_pos a ha (n + 1) (by linarith)
      linarith

  -- and from n = 3, a n is divisible by 4
  have h_a_dvd_by_4 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    ∀ n ≥ 3, 4 ∣ a n := by
    intro n hn
    match n with
    | 0 | 1 | 2 => simp at hn
    | n + 3 =>
      rw [ha]
      have : n + 2 ≥ 2 := by exact Nat.le_add_left 2 n
      have ⟨k, hk⟩ := h_a_even a ha (n + 2) this
      rw [hk, pow_mul, show 2 ^ 2 = 4 by norm_num]
      refine dvd_pow_self 4 ?_
      intro hk'
      rw [hk', mul_zero] at hk
      linarith only [hk, h_a_pos a ha (n + 2) (by linarith)]

  -- especially, we have 4 ∣ a 998
  have h_a_998_dvd_by_4 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    4 ∣ a 998 := h_a_dvd_by_4 a ha 998 (by norm_num)

  -- so a 999 = 2 ^ (a 998) = 2 ^ (4 * k) = 16 ^ k ≡ 1 (mod 5)
  have (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) : a 999 ≡ 1 [ZMOD 5] := by
    have ⟨k, hk⟩ := h_a_998_dvd_by_4 a ha
    rw [ha, hk, pow_mul, show 2 ^ 4 = 16 by norm_num, show (1 : ℤ) = 1 ^ k by ring]
    rw [Nat.cast_pow]
    exact Int.ModEq.pow k rfl

  -- as also a 999 ≡ 0 (mod 4), we deduce that a 999 ≡ 16 (mod 20)
  have h_a_999_mod_20 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    a 999 ≡ 16 [ZMOD 20] := by
    have ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp (this a ha)
    have ⟨k, hk⟩ := h_a_dvd_by_4 a ha 999 (by norm_num)
    rw [hk, Nat.cast_mul, show ↑(4 : ℕ) = (4 : ℤ) by norm_cast] at ht
    have : 4 * k ≡ 1 [ZMOD 5] := by
      rw [ht]
      exact Int.ModEq.symm Int.modEq_add_fac_self
    have : k ≡ -1 [ZMOD 5] := by
      suffices h : (-1) * k ≡ 1 [ZMOD 5] by
        simp at h
        exact Int.neg_modEq_neg.mp h
      trans 4 * k
      · exact Int.ModEq.mul rfl rfl
      exact this
    have ⟨s, hs⟩ := Int.modEq_iff_add_fac.mp this
    have hs' : k = -1 - 5 * s := by linear_combination -hs
    have hk' : a 999 = (4 : ℤ) * k := by norm_cast
    rw [hs'] at hk'
    have : 16 = a 999 + 20 * (1 + s) := by linear_combination -hk'
    apply Int.modEq_iff_add_fac.mpr
    use (1 + s)

  -- note that 2 ^ n ≡ 2 ^ (n % 20) (mod 25) as φ(25) = 20
  have lem_2_pow_mod_20 (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 20) [ZMOD 25] := by
    suffices h : 2 ^ n ≡ 2 ^ (n % 20) [MOD 25] by
      unfold Int.ModEq
      norm_cast
    have : n = n / 20 * 20 + n % 20 := by exact Eq.symm (Nat.div_add_mod' n 20)
    nth_rw 1 [this, show 2 ^ (n % 20) = 1 * 2 ^ (n % 20) by ring]
    rw [pow_add]
    refine Nat.ModEq.mul ?_ (by rfl)
    rw [mul_comm, pow_mul, show 1 = 1 ^ (n / 20) by ring]
    apply Nat.ModEq.pow
    apply Nat.ModEq.pow_totient
    norm_num

  -- so a 1000 = 2 ^ (a 999) ≡ 2 ^ (a 999 % 20) = 2 ^ 16 ≡ 11 (mod 20)
  have h_a_1000_mod_25 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    a 1000 ≡ 11 [ZMOD 25] := by
    rw [ha, Nat.cast_pow, Nat.cast_two]
    have := lem_2_pow_mod_20 (a 999)
    unfold Int.ModEq at h_a_999_mod_20
    norm_cast at h_a_999_mod_20
    norm_num at h_a_999_mod_20
    rw [h_a_999_mod_20 a ha] at this
    exact this

  -- as also a 1000 ≡ 0 (mod 4), we deduce a 1000 ≡ 36 (mod 100)
  have h_a_1000_mod_100 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    a 1000 ≡ 36 [ZMOD 100] := by
    have ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp (h_a_1000_mod_25 a ha)
    have ⟨k, hk⟩ := h_a_dvd_by_4 a ha 1000 (by norm_num)
    rw [hk, Nat.cast_mul, show ↑(4 : ℕ) = (4 : ℤ) by norm_cast] at ht
    have : 4 * k ≡ 11 [ZMOD 25] := by
      rw [ht]
      exact Int.ModEq.symm Int.modEq_add_fac_self
    have : 24 * k ≡ 16 [ZMOD 25] := by
      trans 66
      · rw [show (24 : ℤ) = 6 * 4 by norm_num, show (66 : ℤ) = 6 * 11 by norm_num]
        rw [mul_assoc]
        exact Int.ModEq.mul_left 6 this
      rfl
    have : k ≡ 9 [ZMOD 25] := by
      suffices h : (-1) * k ≡ 16 [ZMOD 25] by
        simp at h
        exact Int.neg_modEq_neg.mp h
      trans 24 * k
      · exact Int.ModEq.mul rfl rfl
      exact this
    have ⟨s, hs⟩ := Int.modEq_iff_add_fac.mp this
    have hs' : k = 9 - 25 * s := by linear_combination -hs
    have hk' : a 1000 = (4 : ℤ) * k := by norm_cast
    rw [hs'] at hk'
    have : 36 = a 1000 + 100 * (s) := by linear_combination -hk'
    apply Int.modEq_iff_add_fac.mpr
    use s

  -- this means that 100 ∣ a 1000 - a 1 is equivalent to say a 1 ≡ 36 (mod 100)
  have h0 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    (100 : ℤ) ∣ a 1000 - a 1 ↔ a 1 ≡ 36 [ZMOD 100] := by
    rw [← Int.modEq_iff_dvd]
    unfold Int.ModEq
    rw [h_a_1000_mod_100 a ha]

  -- and whenever 4 ∣ a 1, we have a 1 ≡ 36 (mod 100) iff a 1 ≡ 11 (mod 25)
  have h1 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) (h_a_1 : 4 ∣ a 1) :
    a 1 ≡ 36 [ZMOD 100] ↔ a 1 ≡ 11 [ZMOD 25] := by
    constructor
    · intro h
      have ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp h
      have : 11 = a 1 + 25 * (4 * k - 1) := by linear_combination hk
      apply Int.modEq_iff_add_fac.mpr
      use 4 * k - 1
    · intro h
      have ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp h
      have ⟨k, hk⟩ := h_a_1
      rw [hk, Nat.cast_mul, show ↑(4 : ℕ) = (4 : ℤ) by norm_cast] at ht
      have : 4 * k ≡ 11 [ZMOD 25] := by
        rw [ht]
        exact Int.ModEq.symm Int.modEq_add_fac_self
      have : 24 * k ≡ 16 [ZMOD 25] := by
        trans 66
        · rw [show (24 : ℤ) = 6 * 4 by norm_num, show (66 : ℤ) = 6 * 11 by norm_num]
          rw [mul_assoc]
          exact Int.ModEq.mul_left 6 this
        rfl
      have : k ≡ 9 [ZMOD 25] := by
        suffices h : (-1) * k ≡ 16 [ZMOD 25] by
          simp at h
          exact Int.neg_modEq_neg.mp h
        trans 24 * k
        · exact Int.ModEq.mul rfl rfl
        exact this
      have ⟨s, hs⟩ := Int.modEq_iff_add_fac.mp this
      have hs' : k = 9 - 25 * s := by linear_combination -hs
      have hk' : a 1 = (4 : ℤ) * k := by norm_cast
      rw [hs'] at hk'
      have : 36 = a 1 + 100 * (s) := by linear_combination -hk'
      apply Int.modEq_iff_add_fac.mpr
      use s

  -- continuing, we notice that a 1 ≡ 11 (mod 25) iff a 0 ≡ 16 (mod 20)
  have h2 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    a 1 ≡ 11 [ZMOD 25] ↔ a 0 ≡ 16 [ZMOD 20] := by
    constructor
    · intro h
      rw [ha, Nat.cast_pow, Nat.cast_two] at h
      have : 2 ^ (a 0 % 20) ≡ 11 [ZMOD 25] := by
        symm
        trans 2 ^ (a 0)
        · exact id (Int.ModEq.symm h)
        exact lem_2_pow_mod_20 (a 0)
      unfold Int.ModEq
      norm_cast
      have _ : a 0 % 20 < 20 := by apply Nat.mod_lt; norm_num
      interval_cases a 0 % 20
      all_goals unfold Int.ModEq at this; norm_num at this
      rfl
    · intro h
      rw [ha, Nat.cast_pow, Nat.cast_two]
      trans 2 ^ (a 0 % 20)
      · exact lem_2_pow_mod_20 (a 0)
      unfold Int.ModEq at h
      norm_cast at h
      rw [h]
      norm_num
      rfl

  -- the condition 4 ∣ a 1 is guaranteed whenever a 0 > 1
  have h3 (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) = 2 ^ (a i)) :
    a 0 > 1 → 4 ∣ a 1 := by
    intro h
    rw [ha]
    generalize a 0 = t at h
    match t with
    | 0 | 1 => norm_num at h
    | n + 2 =>
      rw [add_comm, pow_add, show 2 ^ 2 = 4 by rfl]
      exact Nat.dvd_mul_right 4 (2 ^ n)

  -- so from the above facts we show that the set of feasible n equals to
  -- the numbers in [1, 1000] which equals 16 modulo 20
  have : {n : ℕ | 1 ≤ n ∧ n ≤ 1000 ∧
      ∀ a : ℕ → ℕ, (∀ i, a (i + 1) = 2 ^ (a i)) → a 0 = n → (100 : ℤ) ∣ a 1000 - a 1
    } = {n : ℕ | 1 ≤ n ∧ n ≤ 1000 ∧ n ≡ 16 [ZMOD 20]} := by
    ext n
    constructor
    · rintro ⟨hn₁, hn₂, hn⟩
      simp [hn₁, hn₂]

      have ⟨a, ha, ha0⟩ : ∃ a : ℕ → ℕ, (∀ (i : ℕ), a (i + 1) = 2 ^ a i) ∧ a 0 = n := by
        let a : ℕ → ℕ := fun i ↦ Nat.repeat (fun x ↦ 2 ^ x) i n
        use a
        constructor
        · intro i
          simp [a]
          exact rfl
        simp [a]
        exact rfl

      have ha1 : a 1 ≡ 36 [ZMOD 100] := by
        have := hn a ha ha0
        exact h0 a ha |>.mp this

      by_cases h : n = 1
      · rw [ha, ha0, h] at ha1
        unfold Int.ModEq at ha1
        norm_num at ha1

      have n_gt : n > 1 := by exact Nat.lt_of_le_of_ne hn₁ fun a ↦ h (id (Eq.symm a))
      rw [← ha0] at n_gt
      have := h3 a ha n_gt
      have := h1 a ha this |>.mp ha1
      have := h2 a ha |>.mp this
      rw [ha0] at this
      exact this
    · rintro ⟨hn₁, hn₂, hn⟩
      simp [hn₁, hn₂]
      intro a ha ha0

      have := h0 a ha
      rw [this]

      have : n > 1 := by
        suffices h : n ≠ 1 by exact Nat.lt_of_le_of_ne hn₁ (id (Ne.symm h))
        intro hn1
        rw [hn1] at hn
        unfold Int.ModEq at hn
        norm_num at hn
      rw [← ha0] at this

      have := h3 a ha this
      have := h1 a ha this
      rw [this]
      have := h2 a ha
      rwa [this, ha0]

  rw [this]

  -- clearly there are 1000 / 20 = 50 such numbers, we are done.
  let f (n : ℕ) (h : n < 50) := 20 * n + 16
  apply Set.ncard_eq_of_bijective f
  · intro n ⟨hn₁, hn₂, hn⟩
    have ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hn
    have hnt : n = 20 * (-t) + 16 := by linear_combination -ht
    have : -t ≥ 0 := by
      by_contra! h
      have : 20 * (-t) + 16 > 0 := by rw [← hnt]; exact Int.ofNat_pos.mpr hn₁
      linarith
    have : (-t) = (-t).natAbs := by exact Int.eq_natAbs_of_zero_le this
    rw [this] at hnt
    use (-t).natAbs
    have : (-t).natAbs < 50 := by
      have : 20 * (-t).natAbs + 16 ≤ (1000 : ℤ) := by rw [← hnt]; norm_cast
      by_contra! h
      have : 20 * (-t).natAbs + 16 > (1000 : ℤ) := by
        have : (-t).natAbs ≥ (50 : ℤ) := by
          apply Nat.cast_le.mpr
          exact h
        linarith
      linarith
    use this
    unfold f
    exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) hnt)
  · intro i hi
    unfold f
    simp
    constructor
    · linarith
    rw [add_comm]
    exact Int.modEq_add_fac_self
  intro i j hi hj h_eq
  unfold f at h_eq
  simp at h_eq
  exact h_eq
