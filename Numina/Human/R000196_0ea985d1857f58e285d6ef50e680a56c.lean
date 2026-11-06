import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat


/-
Determine all triplets of prime numbers $p < q < r$ , such that  $p + q = r$ and $(r-p)(q-p)-27p$  is a square.
-/

theorem number_theory_8534 (p q r : ℕ)
    (hpltq : p < q) (hqltr : q < r)
    (hpp : p.Prime) (hqp : q.Prime) (hrp : r.Prime) :
    p + q = r ∧ IsSquare ((r - p) * (q - p) - (27:ℤ) * p) ↔ p = 2 ∧ q = 29 ∧ r = 31 := by

  constructor

  -- sufficiency
  . rintro ⟨hrv, h1'⟩

    have ineq0 : 27 * p ≤ (r - p) * (q - p) := by
      obtain ⟨k, hk⟩ := h1'
      zify
      rw [Nat.cast_sub (by linarith), Nat.cast_sub (by linarith),
          show 27 * (p : ℤ) = (r - p) * (q - p) - k * k by omega]
      exact Int.sub_le_self ((↑r - ↑p) * (↑q - ↑p)) (mul_self_nonneg k)

    have h1 : IsSquare ((r - p) * (q - p) - 27 * p) := by
      obtain ⟨k, hk⟩ := h1'
      use k.natAbs
      zify
      rw [abs_mul_abs_self k, Nat.cast_sub, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub, Nat.cast_sub]
      zify at ineq0
      rw [Nat.cast_sub, Nat.cast_sub] at ineq0
      convert hk
      all_goals linarith

    -- p must equal to two
    have hpv : p = 2 := by
      -- if p ≠ 2, then p, q, r are all odd numbers, which contradicts to p + q = r
      -- hence the sum is even  $odd+odd = even$  which is impossible for prime to be even except 2.
      by_contra hpne
      have hpodd : Odd p := Nat.Prime.odd_of_ne_two hpp hpne
      have hqodd : Odd q := Nat.Prime.odd_of_ne_two hqp (id (Ne.symm (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.Prime.two_le hpp) hpltq))))
      have hrodd : Odd r := Nat.Prime.odd_of_ne_two hrp (id (Ne.symm (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.Prime.two_le hpp) hpltq) hqltr))))
      have hreven : ¬ Odd r := by
        rw [← hrv]
        exact Nat.not_odd_iff_even.mpr (Odd.add_odd hpodd hqodd)
      exact hreven hrodd

    -- replace p with 2 in all states
    simp_all only [hpv]

    -- continue to solve q, r
    rw [isSquare_iff_exists_sq] at h1
    obtain ⟨k, hk⟩ := h1
    rw [← hrv, Nat.add_sub_cancel_left] at hk
    rw [←hrv, Nat.add_sub_cancel_left] at ineq0

    have ineq1 : k < q - 1 := by
      apply lt_of_pow_lt_pow_left' 2

      have r1 : q * (q - 2) < (q - 1) ^ 2 := by
        rw [pow_two]
        zify
        rw [Nat.cast_sub, Nat.cast_sub]
        ring_nf
        omega
        all_goals linarith

      have r2 : k ^ 2 < q * (q - 2) := by
        omega

      exact Nat.lt_trans r2 r1


    have heq1 : (q - 1 - k) * (q - 1 + k) = 55 := by
      norm_num at hk
      zify at hk
      rw [Nat.cast_sub, Nat.cast_mul, Nat.cast_sub] at hk
      zify
      rw [Nat.cast_sub, Nat.cast_sub]
      linear_combination hk
      all_goals linarith

    have heq2 : q = ((q - 1 + k) + 1 + 1 + (q - 1 - k)) / 2 := by
      zify
      nth_rw 2 [Nat.cast_sub]
      ring_nf
      nth_rw 1 [← one_mul 2]
      rw [← add_mul, Int.mul_ediv_cancel, Nat.cast_sub]
      ring
      all_goals linarith

    -- divisors of 55
    have : (q - 1 - k) = 1 ∧ (q - 1 + k) = 55 ∨ (q - 1 - k) = 5 ∧ (q - 1 + k) = 11 := by
      have r : (q - 1 - k) ∈ ({1, 5, 11, 55} : Finset ℕ) := by
        convert Nat.mem_divisors.mpr ⟨Dvd.intro (q - 1 + k) heq1, (by norm_num)⟩
      have r3 : (q - 1 + k) = 55 / (q - 1 - k) :=
        Eq.symm (Nat.div_eq_of_eq_mul_right (by omega) (id (Eq.symm heq1)))
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at r
      rcases r with h | h | h | h
      any_goals norm_num [h, r3]
      any_goals
        simp [h] at r3
        omega

    rcases this with ⟨hadd, hsub⟩ | ⟨hadd, hsub⟩

    -- case (q - 1 - k) = 1 ∧ (q - 1 + k) = 55
    . have hqv : q = 29 := by
        rw [heq2]
        norm_num [hadd, hsub]
      simp [hqv, ← hrv]

    -- case (q - 1 - k) = 5 ∧ (q - 1 + k) = 11
    . have hqv : q = 9 := by
        rw [heq2]
        norm_num [hadd, hsub]
      have hqnp: ¬ q.Prime := by
        have hdvd : 3 ∣ q := by
          rw [hqv]
          exact Nat.dvd_of_mod_eq_zero rfl
        apply Nat.not_prime_of_dvd_of_ne hdvd (by norm_num) (by norm_num [hqv])
      exact False.elim (hqnp hqp)


  -- necessity
  rintro ⟨hpv, hqv, hrv⟩
  constructor
  <;> rw [hpv, hqv, hrv]; native_decide
