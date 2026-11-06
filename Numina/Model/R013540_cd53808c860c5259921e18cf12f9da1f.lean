import Mathlib

theorem number_theory_58248 :
    IsLeast {x | ∃ A B : ℕ, A > 0 ∧ B > 0 ∧ A ≠ B ∧ x = |(A : ℤ) - B| ∧
      (Nat.divisors A).card = (Nat.divisors B).card ∧ (Nat.divisors A).card = (Nat.divisors 2013).card} 1 := by
  constructor
  · -- Show 1 is in the set.
    use 2014, 2013
    all_goals
      native_decide
  · -- Show 1 is the smallest element in the set.
    intro x hx
    rcases hx with ⟨A, B, hA, hB, hne, hx, h1, h2⟩
    have h3 : |(A : ℤ) - (B : ℤ)| ≥ 1 := by
      have h4 : (A : ℤ) ≠ (B : ℤ) := by
        exact_mod_cast hne
      have h5 : (A : ℤ) - (B : ℤ) ≠ 0 := by
        exact sub_ne_zero_of_ne h4
      have h7 : |(A : ℤ) - (B : ℤ)| ≥ 1 := by
        have h8 : (A : ℤ) - (B : ℤ) ≠ 0 := by
          exact h5
        have h9 : |(A : ℤ) - (B : ℤ)| > 0 := by
          apply abs_pos.mpr
          exact h8
        have h10 : |(A : ℤ) - (B : ℤ)| ≥ 1 := by
          omega
        omega
      omega
    omega