import Mathlib

/- define compositie natural number -/
def Nat.Composite (n : ℕ) := n ≠ 1 ∧ ¬n.Prime

theorem number_theory_4496 {n : ℕ} (hn : n > 11) :
    ∃ c1 c2, Nat.Composite c1 ∧ Nat.Composite c2 ∧ c1 + c2 = n := by
  by_cases h : n % 2 = 0
  · -- n is even
    use 4, n - 4
    constructor
    · -- Show 4 is composite
      constructor
      · norm_num
      · norm_num
    constructor
    · -- Show n - 4 is composite
      have h1 : (n - 4) ≠ 1 := by
        omega
      have h2 : ¬ (n - 4).Prime := by
        by_contra h'
        have h3 : (n - 4) > 2 := by
          omega
        have h4 : (n - 4) % 2 = 0 := by
          omega
        have h5 : ¬ (n - 4).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n - 4) by omega) (by omega) (by omega)
        exact h5 h'
      constructor
      · exact h1
      · exact h2
    · -- Show 4 + (n - 4) = n
      omega
  · -- n is odd
    use 9, n - 9
    constructor
    · -- Show 9 is composite
      constructor
      · norm_num
      · norm_num
    constructor
    · -- Show n - 9 is composite
      have h1 : (n - 9) ≠ 1 := by
        omega
      have h2 : ¬ (n - 9).Prime := by
        by_contra h'
        have h3 : (n - 9) > 2 := by
          omega
        have h4 : (n - 9) % 2 = 0 := by
          have h6 : n % 2 = 1 := by
            omega
          omega
        have h5 : ¬ (n - 9).Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n - 9) by omega) (by omega) (by omega)
        exact h5 h'
      constructor
      · exact h1
      · exact h2
    · -- Show 9 + (n - 9) = n
      omega