import Mathlib

theorem number_theory_1551 : {n : ℤ | |n| < 1000 ∧ ∃ m, n = m^2}.encard = 32 := by
  have h1 : {n : ℤ | |n| < 1000 ∧ ∃ m, n = m^2} = Finset.image (fun (m : ℤ) => m ^ 2) (Finset.Icc (-31 : ℤ) 31) := by
    ext n
    simp
    constructor
    · -- First, we show that if n is in the left side, it is in the right side.
      rintro ⟨hn, ⟨m, hm⟩⟩
      rw [hm] at hn
      have h2 : m ^ 2 < 1000 := by
        simpa [abs_lt] using hn
      have h3 : m ≤ 31 := by nlinarith [sq_nonneg m]
      have h4 : m ≥ -31 := by nlinarith [sq_nonneg m]
      refine ⟨m, by omega, by omega⟩
    · -- Now we show the other direction.
      rintro ⟨m, hm, rfl⟩
      have h2 : m ≤ 31 := by
        omega
      have h3 : m ≥ -31 := by
        omega
      constructor
      · -- Show that $|n| < 1000$.
        have h4 : m ^ 2 < 1000 := by nlinarith
        have h5 : |m ^ 2| < 1000 := by
          rw [abs_of_nonneg (show (0 : ℤ) ≤ m ^ 2 by nlinarith)]
          all_goals nlinarith
        simpa [abs_lt] using h5
      · -- Show that ∃ m, n = m^2.
        use m
        all_goals nlinarith
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide