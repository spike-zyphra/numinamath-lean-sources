import Mathlib

theorem number_theory_30321 : ∃ m n, m > 0 ∧ n > 0 ∧ ¬∃ p, p.Prime ∧ p^3 ∣ m ∧
    (∏ i ∈ Finset.Icc 20 28, Nat.factorial i) = m * n^3 := by
  use 825
  use 22815835297819604990427136
  constructor
  · norm_num -- m > 0
  constructor
  · norm_num -- n > 0
  · -- ¬∃ p, p.Prime ∧ p^3 ∣ m ∧ ∏ i ∈ Finset.Icc 20 28, Nat.factorial i = m * n^3
    intro h
    rcases h with ⟨p, hp, hdiv, heq⟩
    have h1 : p^3 ∣ 825 := by
      exact hdiv
    have h2 : p ≤ 825 := by
      have h3 : p^3 ≤ 825 := by
        exact Nat.le_of_dvd (by norm_num) h1
      have h4 : p^3 ≤ 825 := h3
      by_contra h5
      push_neg at h5
      have h6 : p^3 > 825 := by
        have h7 : p ≥ 826 := h5
        have h8 : p^3 ≥ 826^3 := by
          exact Nat.pow_le_pow_of_le_left h7 3
        linarith
      linarith
    interval_cases p <;> norm_num at hp h1 <;> omega