import Mathlib

theorem number_theory_617801 :
    IsLeast {n | 2013 ≤ (Nat.factorial n).divisors.card} 14 := by
  simp only [IsLeast]
  constructor
  · -- Prove 14 works
    simp only [Set.mem_setOf_eq]
    have factor_count_14_factorial : (Nat.factorial 14).divisors.card = 2592 := by
      rw [Nat.card_divisors (by positivity)]
      native_decide
    rw [factor_count_14_factorial]
    decide
  · -- Prove numbers less than 14 don't work
    simp [lowerBounds]
    intro n hn
    contrapose! hn
    -- TODO: ToMathlib
    have factorial_divisors_mono : Monotone (fun n => (Nat.factorial n).divisors) := by
      intro a b hab
      refine Finset.le_iff_subset.mpr ?_
      refine Nat.divisors_subset_of_dvd ?_ ?_
      positivity
      exact Nat.factorial_dvd_factorial hab
    have factorial_divisors_card_mono : Monotone (fun n => (Nat.factorial n).divisors.card) := by
      intro a b hab
      exact Finset.card_le_card (factorial_divisors_mono hab)
    have h13 : (13).factorial.divisors.card < 2013 := by
      rw [Nat.card_divisors (by positivity)]
      native_decide
    apply Nat.lt_of_le_of_lt _ h13
    apply factorial_divisors_card_mono
    exact Nat.le_of_lt_succ hn
