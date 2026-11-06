import Mathlib

theorem number_theory_30321 : ∃ m n, m > 0 ∧ n > 0 ∧ ¬∃ p, p.Prime ∧ p^3 ∣ m ∧
    (∏ i ∈ Finset.Icc 20 28, Nat.factorial i) = m * n^3 := by
  use 825, 6863036196000000000
  constructor
  · norm_num
  constructor
  · norm_num
  · -- Show that m is not divisible by the cube of any prime
    intro h
    rcases h with ⟨p, hp, hp3, heq⟩
    have h1 : p ≤ 825 := by
      have h5 : p^3 ≤ 825 := by
        exact Nat.le_of_dvd (by norm_num) hp3
      by_contra h2
      push_neg at h2
      have h2 : p ≥ 826 := by linarith
      have h3 : p^3 ≥ 826^3 := by
        have h2' : p ≥ 826 := h2
        have : p^3 ≥ 826^3 := by
          apply Nat.pow_le_pow_of_le_left h2' 3
        linarith
      nlinarith
    interval_cases p <;> norm_num at hp hp3 <;> norm_num [Finset.prod_Icc_succ_top, Nat.factorial] at heq ⊢ <;> omega