import Mathlib

theorem number_theory_152428 (a : Fin 5 → ℤ) (h : 25 ∣ ∑ i, (a i) ^ 5) :
    ∃ i, 5 ∣ a i := by

  by_contra h1
  push_neg at h1

  -- For all i, a i not divisible by 5
  have h2 : ∀ i, a i % 5 = 1 ∨ a i % 5 = 2 ∨ a i % 5 = 3 ∨ a i % 5 = 4 := by
    intro i
    have h3 : ¬ (5 ∣ a i) := h1 i
    omega

  -- For all i, a i ^ 5 mod 25
  have h3 : ∀ i, (a i) ^ 5 % 25 = 1 ∨ (a i) ^ 5 % 25 = 7 ∨ (a i) ^ 5 % 25 = 18 ∨ (a i) ^ 5 % 25 = 24 := by
    intro i
    have h4 : a i % 5 = 1 ∨ a i % 5 = 2 ∨ a i % 5 = 3 ∨ a i % 5 = 4 := h2 i
    have h5 : (a i) ^ 5 % 25 = 1 ∨ (a i) ^ 5 % 25 = 7 ∨ (a i) ^ 5 % 25 = 18 ∨ (a i) ^ 5 % 25 = 24 := by
      rcases h4 with (h4 | h4 | h4 | h4)
      · -- a i % 5 = 1
        have h6 : a i % 25 = 1 ∨ a i % 25 = 6 ∨ a i % 25 = 11 ∨ a i % 25 = 16 ∨ a i % 25 = 21 := by
          omega
        rcases h6 with (h6 | h6 | h6 | h6 | h6)
        all_goals
          simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
      · -- a i % 5 = 2
        have h6 : a i % 25 = 2 ∨ a i % 25 = 7 ∨ a i % 25 = 12 ∨ a i % 25 = 17 ∨ a i % 25 = 22 := by
          omega
        rcases h6 with (h6 | h6 | h6 | h6 | h6)
        all_goals
          simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
      · -- a i % 5 = 3
        have h6 : a i % 25 = 3 ∨ a i % 25 = 8 ∨ a i % 25 = 13 ∨ a i % 25 = 18 ∨ a i % 25 = 23 := by
          omega
        rcases h6 with (h6 | h6 | h6 | h6 | h6)
        all_goals
          simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
      · -- a i % 5 = 4
        have h6 : a i % 25 = 4 ∨ a i % 25 = 9 ∨ a i % 25 = 14 ∨ a i % 25 = 19 ∨ a i % 25 = 24 := by
          omega
        rcases h6 with (h6 | h6 | h6 | h6 | h6)
        all_goals
          simp [h6, pow_succ, Int.add_emod, Int.mul_emod]
    assumption

  -- Contradicts that the sum is divisible by 25
  have h4 : (∑ i, (a i) ^ 5) % 25 = 0 := by
    omega

  have h5 : (∑ i, (a i) ^ 5) % 25 = ( (a 0) ^ 5 + (a 1) ^ 5 + (a 2) ^ 5 + (a 3) ^ 5 + (a 4) ^ 5 ) % 25 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    all_goals omega
  rw [h5] at h4

  -- Use that to derive a contradiction
  have h7 : (a 0) ^ 5 % 25 = 1 ∨ (a 0) ^ 5 % 25 = 7 ∨ (a 0) ^ 5 % 25 = 18 ∨ (a 0) ^ 5 % 25 = 24 := h3 0
  have h8 : (a 1) ^ 5 % 25 = 1 ∨ (a 1) ^ 5 % 25 = 7 ∨ (a 1) ^ 5 % 25 = 18 ∨ (a 1) ^ 5 % 25 = 24 := h3 1
  have h9 : (a 2) ^ 5 % 25 = 1 ∨ (a 2) ^ 5 % 25 = 7 ∨ (a 2) ^ 5 % 25 = 18 ∨ (a 2) ^ 5 % 25 = 24 := h3 2
  have h10 : (a 3) ^ 5 % 25 = 1 ∨ (a 3) ^ 5 % 25 = 7 ∨ (a 3) ^ 5 % 25 = 18 ∨ (a 3) ^ 5 % 25 = 24 := h3 3
  have h11 : (a 4) ^ 5 % 25 = 1 ∨ (a 4) ^ 5 % 25 = 7 ∨ (a 4) ^ 5 % 25 = 18 ∨ (a 4) ^ 5 % 25 = 24 := h3 4
  omega