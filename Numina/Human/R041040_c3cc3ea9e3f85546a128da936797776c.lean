import Mathlib

/- Let m be the least positive integer divisible by 17 whose digits sum to 17. Find m. -/
theorem number_theory_85971 :
IsLeast {n | 0 < n ∧ 17 ∣ n ∧ (Nat.digits 10 n).sum = 17} 476 := by {
  -- Proving this is a simple matter of going through the cases one by one, and there isn't much more one can do.
  -- We successively go through the multiples of 17 and compute the digit sum.
  constructor
  -- Here, we show that 476 satisfies the divisibility condition and digit sum.
  simp
  trivial

  -- Now we show that any number satisfying the conditions has to be ≥ 476. We go through all the cases.
  unfold lowerBounds
  simp
  intros k hkp
  intro ⟨n,hkdvd⟩
  intro hkdig
  suffices : n ≥ 28
  linarith
  rw [hkdvd] at hkdig

  match n with
  | 0 => norm_num at hkdig
  | 1 => norm_num at hkdig
  | 2 => norm_num at hkdig
  | 3 => norm_num at hkdig
  | 4 => norm_num at hkdig
  | 5 => norm_num at hkdig
  | 6 => norm_num at hkdig
  | 7 => norm_num at hkdig
  | 8 => norm_num at hkdig
  | 9 => norm_num at hkdig
  | 10 => norm_num at hkdig
  | 11 => norm_num at hkdig
  | 12 => norm_num at hkdig
  | 13 => norm_num at hkdig
  | 14 => norm_num at hkdig
  | 15 => norm_num at hkdig
  | 16 => norm_num at hkdig
  | 17 => norm_num at hkdig
  | 18 => norm_num at hkdig
  | 19 => norm_num at hkdig
  | 20 => norm_num at hkdig
  | 21 => norm_num at hkdig
  | 22 => norm_num at hkdig
  | 23 => norm_num at hkdig
  | 24 => norm_num at hkdig
  | 25 => norm_num at hkdig
  | 26 => norm_num at hkdig
  | 27 => norm_num at hkdig
  | m+28 => {
    linarith
  }
}