import Mathlib


theorem number_theory_25102 :
    IsLeast {t : ℕ | 0 < t ∧ ∃ x : Fin t → ℤ, ∑ i : Fin t, (x i)^3 = 2002^2002} 4 := by
  constructor
  · -- Show 4 is in the set.
    constructor
    · norm_num
    · use fun i =>
        match i with
        | 0 | 1 => 10 * (2002 ^ 667 : ℤ)
        | 2 | 3 => (2002 ^ 667 : ℤ)
        | _ => (0 : ℤ)
      native_decide
  · -- Show 4 is the least.
    intro t ht
    rcases ht with ⟨ht0, x, hx⟩
    by_contra h
    push_neg at h
    have h1 : t = 1 ∨ t = 2 ∨ t = 3 := by
      interval_cases t <;> omega
    rcases h1 with (rfl | rfl | rfl)
    · -- When t = 1
      simp at hx
      have h2 : (x 0) ^ 3 = 2002 ^ 2002 := by
        nlinarith
      have h3 : (x 0) ^ 3 % 9 = 4 := by
        omega
      have h4 : (x 0) ^ 3 % 9 = 0 ∨ (x 0) ^ 3 % 9 = 1 ∨ (x 0) ^ 3 % 9 = -1 ∨ (x 0) ^ 3 % 9 = 8 ∨ (x 0) ^ 3 % 9 = -8 := by
        have h5 : (x 0) % 9 = 0 ∨ (x 0) % 9 = 1 ∨ (x 0) % 9 = 2 ∨ (x 0) % 9 = 3 ∨ (x 0) % 9 = 4 ∨ (x 0) % 9 = 5 ∨ (x 0) % 9 = 6 ∨ (x 0) % 9 = 7 ∨ (x 0) % 9 = 8 := by
          omega
        rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;>
        simp [pow_three, Int.add_emod, Int.mul_emod, h5] at *
      omega
    · -- When t = 2
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hx
      have h2 : (x 0) ^ 3 + (x 1) ^ 3 = 2002 ^ 2002 := by
        nlinarith
      have h3 : ((x 0) ^ 3 + (x 1) ^ 3 : ℤ) % 9 = 4 := by
        omega
      have h4 : (x 0) ^ 3 % 9 = 0 ∨ (x 0) ^ 3 % 9 = 1 ∨ (x 0) ^ 3 % 9 = -1 ∨ (x 0) ^ 3 % 9 = 8 ∨ (x 0) ^ 3 % 9 = -8 := by
        have h5 : (x 0) % 9 = 0 ∨ (x 0) % 9 = 1 ∨ (x 0) % 9 = 2 ∨ (x 0) % 9 = 3 ∨ (x 0) % 9 = 4 ∨ (x 0) % 9 = 5 ∨ (x 0) % 9 = 6 ∨ (x 0) % 9 = 7 ∨ (x 0) % 9 = 8 := by
          omega
        rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;>
        simp [pow_three, Int.add_emod, Int.mul_emod, h5] at *
      have h5 : (x 1) ^ 3 % 9 = 0 ∨ (x 1) ^ 3 % 9 = 1 ∨ (x 1) ^ 3 % 9 = -1 ∨ (x 1) ^ 3 % 9 = 8 ∨ (x 1) ^ 3 % 9 = -8 := by
        have h6 : (x 1) % 9 = 0 ∨ (x 1) % 9 = 1 ∨ (x 1) % 9 = 2 ∨ (x 1) % 9 = 3 ∨ (x 1) % 9 = 4 ∨ (x 1) % 9 = 5 ∨ (x 1) % 9 = 6 ∨ (x 1) % 9 = 7 ∨ (x 1) % 9 = 8 := by
          omega
        rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6) <;>
        simp [pow_three, Int.add_emod, Int.mul_emod, h6] at *
      omega
    · -- When t = 3
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hx
      have h2 : (x 0) ^ 3 + (x 1) ^ 3 + (x 2) ^ 3 = 2002 ^ 2002 := by
        nlinarith
      have h3 : ((x 0) ^ 3 + (x 1) ^ 3 + (x 2) ^ 3 : ℤ) % 9 = 4 := by
        omega
      have h4 : (x 0) ^ 3 % 9 = 0 ∨ (x 0) ^ 3 % 9 = 1 ∨ (x 0) ^ 3 % 9 = -1 ∨ (x 0) ^ 3 % 9 = 8 ∨ (x 0) ^ 3 % 9 = -8 := by
        have h5 : (x 0) % 9 = 0 ∨ (x 0) % 9 = 1 ∨ (x 0) % 9 = 2 ∨ (x 0) % 9 = 3 ∨ (x 0) % 9 = 4 ∨ (x 0) % 9 = 5 ∨ (x 0) % 9 = 6 ∨ (x 0) % 9 = 7 ∨ (x 0) % 9 = 8 := by
          omega
        rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5 | h5) <;>
        simp [pow_three, Int.add_emod, Int.mul_emod, h5] at *
      have h5 : (x 1) ^ 3 % 9 = 0 ∨ (x 1) ^ 3 % 9 = 1 ∨ (x 1) ^ 3 % 9 = -1 ∨ (x 1) ^ 3 % 9 = 8 ∨ (x 1) ^ 3 % 9 = -8 := by
        have h6 : (x 1) % 9 = 0 ∨ (x 1) % 9 = 1 ∨ (x 1) % 9 = 2 ∨ (x 1) % 9 = 3 ∨ (x 1) % 9 = 4 ∨ (x 1) % 9 = 5 ∨ (x 1) % 9 = 6 ∨ (x 1) % 9 = 7 ∨ (x 1) % 9 = 8 := by
          omega
        rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6) <;>
        simp [pow_three, Int.add_emod, Int.mul_emod, h6] at *
      have h6 : (x 2) ^ 3 % 9 = 0 ∨ (x 2) ^ 3 % 9 = 1 ∨ (x 2) ^ 3 % 9 = -1 ∨ (x 2) ^ 3 % 9 = 8 ∨ (x 2) ^ 3 % 9 = -8 := by
        have h7 : (x 2) % 9 = 0 ∨ (x 2) % 9 = 1 ∨ (x 2) % 9 = 2 ∨ (x 2) % 9 = 3 ∨ (x 2) % 9 = 4 ∨ (x 2) % 9 = 5 ∨ (x 2) % 9 = 6 ∨ (x 2) % 9 = 7 ∨ (x 2) % 9 = 8 := by
          omega
        rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7) <;>
        simp [pow_three, Int.add_emod, Int.mul_emod, h7] at *
      omega