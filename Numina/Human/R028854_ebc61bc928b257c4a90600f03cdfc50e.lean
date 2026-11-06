import Mathlib

/- $10 \cdot 10$ Given a four-digit number that satisfies the following conditions:
(1) If the units digit and the hundreds digit, as well as the tens digit and the thousands digit,
are simultaneously swapped, then its value increases by 5940;
(2) When divided by 9, the remainder is 8.
Find the smallest odd number among these four-digit numbers.
(Shandong Province, China Mathematics Competition, 1979) -/
theorem number_theory_277641:
  IsLeast {n:ℕ | n % 9 = 8 ∧ Odd n ∧ n ∈ Finset.Icc 1000 9999 ∧
  (∃ (a b c d: Fin 10), n = 1000*(a:ℕ) + 100*(b:ℕ) + 10*(c:ℕ) + (d:ℕ) ∧
    1000*(c:ℕ) + 100*(d:ℕ) + 10*(a:ℕ) + b = n + 5940) } 1979 := by

  rw [IsLeast, lowerBounds]
  simp only [Finset.mem_Icc, Fin.isValue, zero_mul, add_zero,
    zero_add, Set.mem_setOf_eq, Nat.reduceMod, Nat.reduceLeDiff,
    and_self, Nat.cast_ofNat, true_and, and_imp]

  constructor

  · -- verify 1979 satisfy
    constructor
    · exact Nat.odd_iff.mpr rfl
    · use 1,9,7,9
      norm_cast

  · -- prove 1979 is a lower bound.
    intro n hmod oddn nge nle h
    -- suppose a,b,c,d are digits of n.
    rcases h with ⟨a,b,c,d,hn,heq⟩
    -- by mod 10, we find b = n % 10, or b = d.
    have hbd: b = d := by
      have h1: n + 5940 ≡ n [MOD 10] := by
        have: 5940 ≡ 0 [MOD 10] := rfl
        nth_rw 2 [← add_zero n]
        exact Nat.ModEq.add_left n this
      rw [← heq] at h1
      have h2: 1000*(c:ℕ) + 100*(d:ℕ) + 10*(a:ℕ) =
        10 * (100*c + 10*d + a) := by ring
      rw [h2, ← add_zero n, add_comm n 0] at h1
      have h3: 10 * (100*(c:ℕ) + 10*(d:ℕ) + (a:ℕ)) ≡ 0 [MOD 10] := by
        refine Nat.modEq_zero_iff_dvd.mpr ?_
        apply Nat.dvd_mul_right
      have h4: b ≡ n [MOD 10] := by
        exact Nat.ModEq.add_left_cancel h3 h1
      have h5: n ≡ d [MOD 10] := by
        rw [hn]
        have: 1000*(a:ℕ) + 100*(b:ℕ) + 10*(c:ℕ) =
          10 * (100*a + 10*b + c) := by ring
        rw [this]
        nth_rw 2 [← zero_add (d:ℕ)]
        apply Nat.ModEq.add ?_ rfl
        apply Nat.modEq_zero_iff_dvd.mpr ?_
        apply Nat.dvd_mul_right
      replace h5 := h4.trans h5
      replace h5: (b:ℕ) = d := by
        have: (b:ℕ) % (10:ℕ) = d := by
          apply Nat.mod_eq_of_modEq h5 (by simp)
        rw [← this]
        refine (Nat.mod_eq_of_lt ?_).symm
        simp
      exact Fin.eq_of_val_eq h5

    -- simplify the equation, we find 990(c-a) = 5940
    replace heq: 990*(c-a:ℤ) = 5940 := by
      zify at heq
      rw [hn, hbd] at heq
      push_cast at heq
      linarith only [heq]
    -- cancel 990, c-a = 6
    replace heq: (c-a:ℤ) = 6 := by linarith only [heq]

    -- it's a number of four digits, so a > 0.
    have ha1: (a:ℕ) ≥ 1 := by
      by_contra!
      replace: (a:ℕ) = 0 := Nat.lt_one_iff.mp this
      rw [hn, this, mul_zero] at nge
      linarith only [nge, b.is_le, c.is_le, d.is_le]

    -- since we want the number as small as possible,
    -- we may consider case a = 1.
    by_cases ha2: (a:ℕ) ≥ 2
    · rw [hn]
      linarith only [ha2]
    replace ha2: (a:ℕ) = 1 := by
      push_neg at ha2
      exact Nat.eq_of_le_of_lt_succ ha1 ha2
    -- and therefore c-a = 6 gives c = 7
    have ceq: (c:ℕ) = 7 := by
      zify
      rw [ha2] at heq
      norm_num at heq
      linarith only [heq]

    -- and notice that number mod 9 equal to add its each digits.
    have nmod9: n ≡ (a:ℕ) + b + c + d [MOD 9] := by
      rw [hn]
      have ha: 1000*(a:ℕ) ≡ 1*a [MOD 9] := by
        apply Nat.ModEq.mul ?_ rfl
        rfl
      have hb: 100*(b:ℕ) ≡ 1 * b [MOD 9] := by
        apply Nat.ModEq.mul ?_ rfl
        rfl
      have hc: 10*(c:ℕ) ≡ 1*c [MOD 9] := by
        apply Nat.ModEq.mul ?_ rfl
        rfl
      simp only [one_mul] at ha hb hc
      refine Nat.ModEq.add_right _ ?_
      apply Nat.ModEq.add ?_ hc
      apply ha.add hb

    -- so a+b+c+d mod 9 is 8.
    -- when a = 1, c = 7, we have b + d mod 9 is 0, or 9 divide 2b
    replace hmod: 2*d ≡ 0 [MOD 9] := by
      change n ≡ 8 [MOD 9] at hmod
      replace hmod := nmod9.symm.trans hmod
      rw [add_comm _ (c:ℕ), ← add_assoc, ha2, ceq,
      hbd, add_assoc _ (d:ℕ) _, ← two_mul, ← add_zero 8] at hmod
      apply Nat.ModEq.add_left_cancel ?_ hmod
      rfl
    rw [Nat.modEq_zero_iff_dvd] at hmod
    rw [Nat.Coprime.dvd_mul_left (by norm_num)] at hmod

    -- 9 divide d, then d = 9 or 0.
    -- but n is odd, d cannot be 0, so d = 9
    have dnz: (d:ℕ) ≠ 0 := by
      rintro deq
      rw [ha2, ceq, hbd, deq] at hn
      rw [hn] at oddn
      absurd oddn
      exact Nat.not_odd_iff.mpr rfl
    have dpos: 0 < (d:ℕ) := Nat.zero_lt_of_ne_zero dnz
    have := Nat.le_of_dvd dpos hmod
    replace: (d:ℕ) = 9 := le_antisymm d.is_le this

    -- then we solve n = 1979
    simp [hn, ha2, hbd, ceq, this]