import Mathlib

theorem number_theory_13955 (a : ℕ → ℤ) (ha : ∑ i ∈ Finset.range 24, a i = 0)
    (h : ∀ i ∈ Finset.range 24, |a i| ≤ i + 1) :
    ∑ i ∈ Finset.range 24, (i + 1) * a i ≤ 1432 := by
  have h1 : ∀ i ∈ Finset.range 24, - (i + 1 : ℤ) ≤ a i ∧ a i ≤ i + 1 := by
    intro i hi
    have h2 := h i hi
    cases' abs_le.mp h2 with h3 h4
    omega

  have h2 : ∑ i ∈ Finset.range 24, (i + 1) * a i ≤ 1432 := by
    norm_num [Finset.sum_range_succ] at *
    have h40 : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 + a 13 + a 14 + a 15 + a 16 + a 17 + a 18 + a 19 + a 20 + a 21 + a 22 + a 23 = 0 := by
      norm_num [Finset.sum_range_succ] at ha ⊢
      all_goals
        linarith [ha]

    have h41 : -1 ≤ a 0 ∧ a 0 ≤ 1 := by
      have h1' := h1 0 (by simp)
      omega

    have h42 : -2 ≤ a 1 ∧ a 1 ≤ 2 := by
      have h1' := h1 1 (by simp)
      omega

    have h43 : -3 ≤ a 2 ∧ a 2 ≤ 3 := by
      have h1' := h1 2 (by simp)
      omega

    have h44 : -4 ≤ a 3 ∧ a 3 ≤ 4 := by
      have h1' := h1 3 (by simp)
      omega

    have h45 : -5 ≤ a 4 ∧ a 4 ≤ 5 := by
      have h1' := h1 4 (by simp)
      omega

    have h46 : -6 ≤ a 5 ∧ a 5 ≤ 6 := by
      have h1' := h1 5 (by simp)
      omega

    have h47 : -7 ≤ a 6 ∧ a 6 ≤ 7 := by
      have h1' := h1 6 (by simp)
      omega

    have h48 : -8 ≤ a 7 ∧ a 7 ≤ 8 := by
      have h1' := h1 7 (by simp)
      omega

    have h49 : -9 ≤ a 8 ∧ a 8 ≤ 9 := by
      have h1' := h1 8 (by simp)
      omega

    have h50 : -10 ≤ a 9 ∧ a 9 ≤ 10 := by
      have h1' := h1 9 (by simp)
      omega

    have h51 : -11 ≤ a 10 ∧ a 10 ≤ 11 := by
      have h1' := h1 10 (by simp)
      omega

    have h52 : -12 ≤ a 11 ∧ a 11 ≤ 12 := by
      have h1' := h1 11 (by simp)
      omega

    have h53 : -13 ≤ a 12 ∧ a 12 ≤ 13 := by
      have h1' := h1 12 (by simp)
      omega

    have h54 : -14 ≤ a 13 ∧ a 13 ≤ 14 := by
      have h1' := h1 13 (by simp)
      omega

    have h55 : -15 ≤ a 14 ∧ a 14 ≤ 15 := by
      have h1' := h1 14 (by simp)
      omega

    have h56 : -16 ≤ a 15 ∧ a 15 ≤ 16 := by
      have h1' := h1 15 (by simp)
      omega

    have h57 : -17 ≤ a 16 ∧ a 16 ≤ 17 := by
      have h1' := h1 16 (by simp)
      omega

    have h58 : -18 ≤ a 17 ∧ a 17 ≤ 18 := by
      have h1' := h1 17 (by simp)
      omega

    have h59 : -19 ≤ a 18 ∧ a 18 ≤ 19 := by
      have h1' := h1 18 (by simp)
      omega

    have h60 : -20 ≤ a 19 ∧ a 19 ≤ 20 := by
      have h1' := h1 19 (by simp)
      omega

    have h61 : -21 ≤ a 20 ∧ a 20 ≤ 21 := by
      have h1' := h1 20 (by simp)
      omega

    have h62 : -22 ≤ a 21 ∧ a 21 ≤ 22 := by
      have h1' := h1 21 (by simp)
      omega

    have h63 : -23 ≤ a 22 ∧ a 22 ≤ 23 := by
      have h1' := h1 22 (by simp)
      omega

    have h64 : -24 ≤ a 23 ∧ a 23 ≤ 24 := by
      have h1' := h1 23 (by simp)
      omega

    omega
  exact h2