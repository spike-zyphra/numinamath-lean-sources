import Mathlib


/- A positive integer $\overline{A B C}$, where $A, B, C$ are digits, satisfies

$$
\overline{A B C}=B^{C}-A
$$

Find $\overline{A B C}$.-/
theorem number_theory_609595{A B C: ℕ}
  (Alt: A < 10) (Blt: B < 10) (Clt: C < 10)
  (heq: ↑(Nat.ofDigits 10 [C, B, A]: ℕ) = B^C - (A:ℤ))
  (hpos: 0 < Nat.ofDigits 10 [C, B, A]):
  Nat.ofDigits 10 [C, B, A] = 127 := by

  -- if a1 ≥ a2 and b1 ≥ b2, then a1^b1 ≥ a2^b2
  have lemma_pow_le {a1 b1 a2 b2: ℕ} (h1: a1 ≥ a2)
    (h2: b1 ≥ b2) (a1pos: 0 < a1): a1^b1 ≥ a2^b2 := by
    apply le_trans ?_ (Nat.pow_le_pow_right a1pos h2)
    apply Nat.pow_le_pow_left h1

  -- obviously, number overline ABC = 100A + 10B + C
  have: Nat.ofDigits 10 [C, B, A] = 100*A + 10*B + C := by
    simp only [Nat.ofDigits, Nat.cast_id, mul_zero, add_zero]
    ring
  rw [this] at heq hpos ⊢

  -- we claim impossible for A = 0
  have A_not_zero: A ≠ 0 := by
    -- suppose on the contrary
    rintro rfl
    simp only [mul_zero, zero_add, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, CharP.cast_eq_zero, sub_zero] at heq hpos
    -- then given condition turns to 10B + C = B^C
    norm_cast at heq hpos
    -- impossible for C = 0
    have hC: C ≠ 0 := by
      rintro rfl
      -- otherwise, 10B + 0 = B^0 and 0 < 10B + 0.
      -- 0 < B, then B^0 = 1. impossible for 10B = 1.
      simp only [add_zero, Nat.ofNat_pos, mul_pos_iff_of_pos_left] at hpos
      simp at heq
    -- by mod B, we find B must divide C, therefore B ≤ C.
    have hBC: B ≤ C := by
      have h1: B ∣ B^C := dvd_pow_self B hC
      have h2: B ∣ 10*B := Nat.dvd_mul_left B 10
      rw [← heq] at h1
      apply Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hC) ?_
      exact (Nat.dvd_add_iff_right h2).mpr h1
    -- B,C are digits of natrual number in base 10, they both < 10
    -- so 10B+C < 100
    have h1: 10*B + C < 100 := by linarith only [Blt, Clt]
    -- then B ≤ 3, otherwise B^C ≥ B^B ≥ 4^4  > 100.
    have h2: B ≤ 3 := by
      by_contra! hB
      replace hB : B ≥ 4 := by exact hB
      have posB: 0 < B := Nat.zero_lt_of_lt hB
      have not_h1: B^C ≥ 4^4 := by
        apply lemma_pow_le hB (le_trans hB hBC) posB
      rw [heq] at h1
      linarith only [h1, not_h1]
    -- verify B = 0,1,2,3. and we find none of these values are possible.
    interval_cases B
    · -- impossible for C = 0, since we already prove C ≠ 0.
      simp [hC] at heq
    · simp only [mul_one, one_pow] at heq
      -- impossible for 10+C = 1.
      linarith only [heq]
    · -- 30 > 20+C = 2^C, so C < 5.
      have hC: C < 5 := by
        by_contra! Cge
        replace h2: 2^C ≥ 2^5 := Nat.pow_le_pow_right (by norm_num) Cge
        have h3: 2^C < 30 := by
          rw [← heq]
          linarith only [Clt]
        linarith only [h2, h3]
      replace hC: C ≤ 4 := Nat.le_of_lt_succ hC
      -- try C = 0,1,2,3,4. none of this satisfy 20+C = 2^C.
      clear * - hC heq
      revert heq
      revert C
      decide
    · -- 3^3 < 30+C < 3^4, so 3 < C < 4, contradiction.
      have hC1: 3 < C := by
        by_contra! Cle
        have: 3^C ≤ 3^3 := Nat.pow_le_pow_right (by norm_num) Cle
        rw [← heq] at this
        linarith only [this]
      have hC2: C < 4 := by
        by_contra! Cge
        have: 3^4 ≤ 3^C := Nat.pow_le_pow_right (by norm_num) Cge
        rw [← heq] at this
        linarith only [this, Clt]
      omega

  have Age: A ≥ 1 := Nat.one_le_iff_ne_zero.mpr A_not_zero

  -- 100A + 10B + C = B^C - A, or 101A+C + 10B = B^C
  -- or, 101A = B^C-10B-C, 101 ∣ B^C - 10B - C
  replace heq: (101:ℤ)*A = B^C - 10*B - C := by
    push_cast at heq
    linarith only [heq]
  have hdvd: (101:ℤ) ∣ B^C - 10*B - C := by
    rw [← heq]
    exact Int.dvd_mul_right 101 _
  -- easy to find upper and lower bound for B^C - 10B - C.
  have BClb: 101 ≤ B^C - 10*B - (C:ℤ) := by
    rw [← heq]
    linarith only [Age]
  -- A < 10, or A ≤ 9. 101A ≤ 101x9 < 1000.
  have BCub: B^C - 10*B - (C:ℤ) < 1000 := by
    rw [← heq]
    linarith only [Alt, Blt, Clt]
  -- C ≠ 0, because when A ≥ 1, B^C ≥ 100
  have Cnz: C ≠ 0 := by
    rintro rfl
    simp only [pow_zero, CharP.cast_eq_zero, sub_zero] at BClb
    linarith only [BClb]
  have Cge: C ≥ 1 := Nat.one_le_iff_ne_zero.mpr Cnz

  -- consider value of B.

  -- first, we work on B ≥ 5 case.
  by_cases hB: B ≥ 5
  · have Ble: B ≤ 9 := Nat.le_of_lt_succ Blt
    -- when B ≥ 5, C < 5, otherwise 5^5 > 1000.
    replace Clt: C < 5 := by
      by_contra! Cge
      have: B^C ≥ 5^5 := lemma_pow_le hB Cge (by linarith only [hB])
      linarith only [this, BCub, Blt, Clt]
    replace Clt: C ≤ 4 := Nat.le_of_lt_succ Clt
    clear * - Cge Clt hB Ble hdvd
    -- test all values B,C, we see none of them satisfy 101 divide B^C - 10B - C.
    -- contradiction.
    absurd hdvd
    interval_cases B
    all_goals
      clear A B hdvd hB Ble
      -- B = 5,6,7,8,9; C = 1,2,3,4. here 5x4 = 20 cases in total to decide.
      decide +revert

  · -- move to B ≤ 4 case.
    replace hB: B ≤ 4 := Nat.le_of_not_lt hB
    have Cle: C ≤ 9 := by exact Nat.le_of_lt_succ Clt
    -- 4^3 = 64 < 100, so C ≥ 4 must hold
    have hC: C > 3 := by
      by_contra! Cle
      have h1: B^C ≤ 4^3 := by
        apply lemma_pow_le hB Cle (by norm_num)
      linarith only [h1, BClb]
    replace hC: C ≥ 4 := by exact hC
    -- for 101 divide B^C - 10B - C, we find (B,C) = (2,7) or (4,9).
    -- but 4^9 > upper bound, contradiction. so only solution is B=2, C=7.
    have h1: ¬ (101:ℤ) ∣ B^C - 10*B - C ∨ (B=2 ∧ C=7) ∨ (B=4 ∧ C=9) := by
      clear * - hC Cle hB hdvd
      interval_cases B
      all_goals
        clear B hB hdvd
        -- B = 0,1,2,3,4, and C = 4,5,6,7,8. here 25 cases in total to decide.
        decide +revert
    rcases h1 with h1 | h1 | h1
    · contradiction
    · -- when B=2, C=7, substitute into 101A = B^C - 10B-C, we get A = 1.
      simp only [h1, Nat.cast_ofNat, Int.reducePow, Int.reduceMul,
      Int.reduceSub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_eq_left₀, Nat.cast_eq_one] at heq
      -- therefore 100A+10B+C = 100x1 + 10x2 + 7 = 127
      simp [h1, heq]
    · -- B=4, C=9 is impossible. since it exceeds upper bound.
      simp [h1] at BCub