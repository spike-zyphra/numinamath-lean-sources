import Mathlib


/- What is the sum of all of the two-digit primes that are greater than 12 but less than 99 and are still prime when their two digits are interchanged? -/
theorem number_theory_13618
    (two_digit_primes valid_primes : Finset ℕ)
    (def_two_digit_primes : two_digit_primes = (Finset.Icc 13 99).filter (fun x => x.Prime))
    (def_valid_primes : valid_primes = two_digit_primes.filter (fun x => ((x % 10) * 10 + (x / 10)).Prime)) :
    valid_primes.sum id = 418 := by

  -- A two-digit prime could end in 1, 3, 7 or 9;
  have r1 : ∀ x ∈ two_digit_primes, (x % 10) ∈ ({1, 3, 5, 7, 9} : Finset ℕ) := by
    intro x hx
    rw [def_two_digit_primes, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, _⟩, hxp⟩ := hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have : Odd (x % 10) := by
      refine Nat.odd_iff.mpr ?_
      rw [Nat.mod_mod_of_dvd x (by norm_num)]
      rcases Nat.Prime.eq_two_or_odd' hxp with h | h
      . linarith
      . exact Nat.odd_iff.mp h
    have : x % 10 < 10 := by refine Nat.mod_lt x (by linarith)
    interval_cases (x % 10)
    any_goals simp
    any_goals contradiction

  -- thus, we need to examine primes only in the 10s, 30s, 70s and 90s because when the digits are switched the tens digit will become the units digit.
  have r2 : ∀ x ∈ valid_primes, (x / 10) ∈ ({1, 3, 5, 7, 9} : Finset ℕ) := by
    intro x hx
    simp [def_valid_primes, Finset.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    specialize r1 x hx1
    set y := (x % 10 * 10 + x / 10) with hy
    simp [def_two_digit_primes] at hx1
    obtain ⟨⟨hxge, hxle⟩, hxp⟩ := hx1
    have hymod : y % 10 = x / 10 := by omega
    have hymododd: Odd (y % 10) := by
      refine Nat.odd_iff.mpr ?_
      rw [Nat.mod_mod_of_dvd y (by norm_num)]
      rcases Nat.Prime.eq_two_or_odd' hx2 with h | h
      . rw [show x = 20 by omega] at hxp
        contradiction
      . exact Nat.odd_iff.mp h
    have : x / 10 < 10 := Nat.div_lt_of_lt_mul (by linarith)
    rw [← hymod] at this
    rw [← hymod]
    interval_cases (y % 10)
    any_goals simp
    any_goals contradiction

  -- The primes greater than 12 but less than 99 that are still prime when their two digits are interchanged are 13, 17, 31, 37, 71, 73, 79 and 97.
  have r3 : valid_primes = {13, 17, 31, 37, 71, 73, 79, 97} := by
    rw [def_valid_primes, def_two_digit_primes]
    native_decide

  -- Their sum is $\boxed{418}$.
  rw [r3]
  exact rfl
