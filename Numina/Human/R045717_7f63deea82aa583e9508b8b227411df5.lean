import Mathlib


/- 175. A divisor of its palindrome. In what base does 792 divide 297? -/
theorem number_theory_270199 {b:ℕ} (hb: b ≥ 10):
  Nat.ofDigits b [7, 9, 2] ∣ Nat.ofDigits b [2, 9, 7] ↔
  b = 19 := by

  -- we will prove that 2 x 297 < 792 < 4 x 297 for any base b ≥ 10.


  -- notice that 200 < 297 < 300
  have h1: Nat.ofDigits b [0,0,2] < Nat.ofDigits b [7,9,2] := by
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero,
    add_zero, zero_add]
    linarith only [hb]
  have h2: Nat.ofDigits b [7,9,2] < Nat.ofDigits b [0,0,3] := by
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil,
    mul_zero, add_zero, zero_add]
    zify at hb ⊢
    suffices (b:ℤ)*(b-9) > 7 by
      linarith only [this]
    have: (b:ℤ) * (b-9) ≥ b * 1 := by
      refine Int.mul_le_mul_of_nonneg_left ?_ ?_
      <;> linarith only [hb]
    linarith only [this, hb]

  -- then 2 x 297 < 2 x 300 = 600 < 797
  have h3: 2 * Nat.ofDigits b [7,9,2] <
    Nat.ofDigits b [2,9,7] := by
    have hh1: Nat.ofDigits b [0,0,6] < Nat.ofDigits b [2,9,7] := by
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil,
      mul_zero, add_zero, zero_add]
      linarith only [sq_nonneg b, hb]
    have hh2: Nat.ofDigits b [0,0,6] = 2 * Nat.ofDigits b [0,0,3] := by
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil,
      mul_zero, add_zero, zero_add]
      ring
    rw [hh2] at hh1
    apply lt_trans ?_ hh1
    exact Nat.mul_lt_mul_of_pos_left h2 (by norm_num)

  -- and 797 < 800 = 4 x 200 < 4 x 297
  have h4: Nat.ofDigits b [2,9,7] < 4 * Nat.ofDigits b [7,9,2] := by
    have: Nat.ofDigits b [2,9,7] < Nat.ofDigits b [0,0,8] := by
      simp only [Nat.ofDigits, Nat.cast_ofNat,
      mul_zero, add_zero, CharP.cast_eq_zero, zero_add]
      zify
      suffices (b:ℤ)*(b-9) > 2 by
        linarith only [this]
      have: (b:ℤ) * (b-9) ≥ b * 1 := by
        refine Int.mul_le_mul_of_nonneg_left ?_ ?_
        <;> linarith only [hb]
      linarith only [this, hb]
    refine this.trans ?_
    replace: Nat.ofDigits b [0,0,8] = 4 * Nat.ofDigits b [0,0,2] := by
      simp only [Nat.ofDigits, CharP.cast_eq_zero,
      Nat.cast_ofNat, mul_zero, add_zero, zero_add]
      ring
    rw [this]
    refine Nat.mul_lt_mul_of_pos_left h1 (by norm_num)

  -- therefore if 297 divide 797, then must be the case 797 = 3 x 297

  constructor

  · rintro ⟨k,hk⟩
    have keq: k = 3 := by
      rw [hk, mul_comm _ k] at h3 h4
      have pos200: 0 < Nat.ofDigits b [0,0,2] := by
        have: 0 < b := by linarith only [hb]
        simp [Nat.ofDigits, this]
      have pos297 := pos200.trans h1
      have hk1: k < 4 := (Nat.mul_lt_mul_right pos297).mp h4
      have hk2: 2 < k := (Nat.mul_lt_mul_right pos297).mp h3
      exact Nat.eq_of_le_of_lt_succ hk2 hk1
    -- from equation 797 = 3 x 297, we can solve b.
    have heq: 7*b^2 + 9*b + 2 = 6*b^2 + 27*b + 21 := by
      simp only [Nat.ofDigits, Nat.cast_ofNat,
      mul_zero, add_zero, keq] at hk
      linarith only [hk]
    -- simplify
    replace heq: (b-19)*(b+1:ℤ) = 0 := by
      zify at heq
      linarith only [heq]
    -- then b = 19, since b is digit ≥ 10 cannot be -1.
    have: (b:ℤ) + 1 ≠ 0 := by
      apply ne_of_gt (by linarith only [hb])
    simp only [mul_eq_zero, this, or_false] at heq
    linarith only [heq]

  · -- verify when base is 19, 297 divide 792
    rintro rfl
    norm_num [Nat.ofDigits]