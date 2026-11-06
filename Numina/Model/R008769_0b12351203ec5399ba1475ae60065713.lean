import Mathlib


theorem number_theory_13618
    (two_digit_primes valid_primes : Finset ℕ)
    (def_two_digit_primes : two_digit_primes = (Finset.Icc 13 99).filter (fun x => x.Prime))
    (def_valid_primes : valid_primes = two_digit_primes.filter (fun x => ((x % 10) * 10 + (x / 10)).Prime)) :
    valid_primes.sum id = 418 := by
  rw [def_valid_primes, def_two_digit_primes]
  native_decide