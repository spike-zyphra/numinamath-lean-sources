import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
set_option maxRecDepth 10000

/- Find all non-negative integers  $ m$  and  $ n$  that satisfy the equation:
\[ 107^{56}(m^2\minus{}1)\minus{}2m\plus{}5\equal{}3\binom{113^{114}}{n}\]
(If  $ n$  and  $ r$  are non-negative integers satisfying  $ r\le n$ ,
then  $ \binom{n}{r}\equal{}\frac{n}{r!(n\minus{}r)!}$  and  $ \binom{n}{r}\equal{}0$  if  $ r>n$ .)-/
theorem number_theory_8563 :
  ∀ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ 107^56 * (m^2 - 1) - 2 * m + 5 = 3 * Nat.choose (113^114) n.natAbs
    → (m ≡ 1 [ZMOD 113] ∨ m ≡ 110 [ZMOD 113] ∧ n = 0 ∨ n = 113^114) ∨ m ≡ 31 [ZMOD 113] ∨ m ≡ 80 [ZMOD 113]:= by
      intro m n h
      have h1 : 107^56 * (m^2 - 1) - 2 * m + 5 ≡ 3 * (113^114).choose n.natAbs [ZMOD 113] := by
          rw [h.2.2]
      -- $107^ 56 \equiv -1 \pmod {113}$
      have h2 : 107^ 56 ≡ -1 [ZMOD 113] := by decide
      -- case $n =0 or  n = 113^114$ : in this condition, simplify the equation we can get
      -- \[
      -- 107^{56}(m^2 - 1) - 2m + 5 = 3.
      -- \]
      by_cases h3 : n = 0 ∨ n = 113^114
      have h3' : (3 * ((113 ^ 114).choose n.natAbs) : ℤ) = 3 := by
        rcases h3 with h3 | h3 <;> simp [h3]
      · simp only [h3', Int.natAbs_zero, choose_zero_right, Nat.cast_one, mul_one] at h1
        have : 107 ^ 56 * (m ^ 2 - 1) ≡ -1 * (m ^ 2 - 1) [ZMOD 113]:=
          Int.ModEq.mul h2 Int.ModEq.rfl
        replace := Int.ModEq.sub this (Int.ModEq.rfl (a := 2 * m))
        replace := Int.ModEq.add this (Int.ModEq.rfl (a := 5))
        replace := this.symm.trans h1
        have := Int.ModEq.dvd this
        simp at this
        have c1 : 3 ≡ m^2 + 2 * m [ZMOD 113] := by
          apply Int.modEq_of_dvd
          convert this using 1
          ring_nf
        have : m % 113 < 113 := Int.emod_lt_of_pos m (by simp)
        have : 0 ≤ m % 113 := Int.emod_nonneg m (by simp)
        have c2 : m ^ 2 + 2 * m ≡ (m % 113) ^ 2 + 2 * (m % 113) [ZMOD 113] :=
          Int.ModEq.add (Int.ModEq.pow 2 <| Int.ModEq.symm (Int.mod_modEq m 113))
            (Int.ModEq.mul rfl (Int.ModEq.symm (Int.mod_modEq m 113)))
        replace c1 := c1.trans c2
        set k := (m % 113) with hk
        -- solve the equation
        -- \[
        -- 107^{56}(m^2 - 1) - 2m + 5 = 3.
        -- \], we get m = 1, so $m \equiv \pmod{113}$.
        rcases h3 with h3 | h3
        · simp [h3, -Int.reducePow] at h
          have : m ≤ 1 := by nlinarith
          have : 0 ≤ m := h.1
          interval_cases m <;> tauto
        · rw [h3, show (113^114 : ℤ).natAbs = 113^114 by norm_cast] at h
          simp [-Int.reducePow, -reducePow] at h
          have : m ≤ 1 := by nlinarith
          have : 0 ≤ m := h.1
          interval_cases m <;> tauto
      · -- case $n \ne 0 and n \ne 113^114$ : $113 \mid 3\binom{113^{114}}{n}$,
        push_neg at h3
        have : (113 : ℤ) ∣ 3 * ((113 ^ 114).choose n.natAbs) := by
          norm_cast
          apply dvd_mul_of_dvd_right
          exact Nat.Prime.dvd_choose_pow (show (113).Prime by
            exact properDivisors_eq_singleton_one_iff_prime.mp rfl)
            (Int.natAbs_ne_zero.mpr h3.1) (by
              intro tmp
              rw [←Int.natAbs_ofNat (113^114), Int.natAbs_eq_natAbs_iff, or_iff_left ] at tmp
              have : n = 113^114 := by norm_cast
              exact h3.2 this
              intro tmp; have : n = -113^114 := by norm_cast
              linarith)
        have : 3 * (113 ^ 114).choose n.natAbs ≡ 0 [ZMOD 113] :=
          Dvd.dvd.modEq_zero_int this
        -- so $113 \mid 107 ^ 56 * (m ^ 2 - 1) - 2 * m + 5$,
        -- i.e. `107 ^ 56 * (m ^ 2 - 1) ≡ -1 * (m ^ 2 - 1) [ZMOD 113]`
        replace h1 := h1.trans this
        have : 107 ^ 56 * (m ^ 2 - 1) ≡ -1 * (m ^ 2 - 1) [ZMOD 113]:=
          Int.ModEq.mul h2 Int.ModEq.rfl
        replace := Int.ModEq.sub this (Int.ModEq.rfl (a := 2 * m))
        replace := Int.ModEq.add this (Int.ModEq.rfl (a := 5))
        replace := this.symm.trans h1
        simp at this
        -- simplifying, $m ^ 2 + 2 * m \equiv 6 \pmod {113}$. Solve this equation we get
        -- $m \equiv 31 \pmod {113} ∨ m \equiv 80 \pmod {113}$
        have c1 : m ^ 2 + 2 * m ≡ 6 [ZMOD 113] := by
          rw [sub_sub, sub_add_eq_add_sub] at this
          simp at this
          have := (Int.ModEq.add this (Int.ModEq.rfl (a := m^2 + 2 * m))).symm
          simp at this
          exact this
        have : m % 113 < 113 := Int.emod_lt_of_pos m (by simp)
        have : 0 ≤ m % 113 := Int.emod_nonneg m (by simp)
        have c2 : m ^ 2 + 2 * m ≡ (m % 113) ^ 2 + 2 * (m % 113) [ZMOD 113] :=
          Int.ModEq.add (Int.ModEq.pow 2 <| Int.ModEq.symm (Int.mod_modEq m 113))
            (Int.ModEq.mul rfl (Int.ModEq.symm (Int.mod_modEq m 113)))
        replace c1 := c2.symm.trans c1
        set k := (m % 113) with hk
        interval_cases k <;> (simp at c1; tauto)
