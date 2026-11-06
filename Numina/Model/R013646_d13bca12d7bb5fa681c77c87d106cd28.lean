import Mathlib


open Int


lemma lemma_1 (n : ℤ) (h : n ^ 2 + n + 1 ∣ 2 * n + 3) :
    n ≤ 2 ∧ -1 ≤ n := by
  have h1 : n ^ 2 + n + 1 ∣ 2 * n + 3 := h

  have h10 : n ≤ 2 := by
    by_contra h14
    push_neg at h14
    have h11 : n ≥ 3 := by omega
    have h14 : n > 2 := by linarith
    rcases h1 with ⟨k, hk⟩
    have h15 : k * (n ^ 2 + n + 1) = 2 * n + 3 := by
      linarith
    have h16 : k > 0 := by
      nlinarith [sq_nonneg (n + 1), sq_pos_of_pos (show 0 < n by nlinarith), sq_nonneg (n ^ 2 + n + 1)]
    have h17 : k ≤ 0 := by
      nlinarith [sq_nonneg (n - 1), sq_nonneg (n + 1), sq_nonneg (n ^ 2 + n + 1), sq_nonneg (k * n), sq_nonneg (k * (n ^ 2 + n + 1) - (2 * n + 3))]
    linarith

  have h11 : -1 ≤ n := by
    by_contra h22
    push_neg at h22
    have h222 : n ≤ -2 := by omega
    rcases h1 with ⟨k, hk⟩
    have h23 : k * (n ^ 2 + n + 1) = 2 * n + 3 := by
      linarith
    have h24 : k ≥ 0 := by
      nlinarith [sq_nonneg (n + 1), sq_nonneg (n ^ 2 + n + 1), sq_pos_of_pos (show 0 < n ^ 2 + n + 1 by nlinarith)]
    have h25 : k * (n ^ 2 + n + 1) ≥ 0 := by
      nlinarith [sq_nonneg (n + 1), sq_nonneg (n ^ 2 + n + 1), sq_pos_of_pos (show 0 < n ^ 2 + n + 1 by nlinarith)]
    nlinarith

  exact ⟨h10, h11⟩


theorem number_theory_7635 : {n : ℤ | n ^ 2 + n + 1 ∣ 2 * n + 3} = {-1, 0, 2} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward: If n in the set, n divides.
    intro h
    have h1 : n ^ 2 + n + 1 ∣ 2 * n + 3 := h
    have h9 : n ≤ 2 ∧ -1 ≤ n := lemma_1 n h1
    have h11 : n ≤ 2 := h9.1
    have h12 : n ≥ -1 := h9.2
    have h13 : n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by 
      omega
    rcases h13 with (h14 | h14 | h14 | h14)
    · -- n = -1
      rw [h14]
      all_goals simp
    · -- n = 0
      rw [h14]
      all_goals simp
    · -- n = 1
      rw [h14] at h1
      norm_num at h1
    · -- n = 2
      rw [h14]
      all_goals simp
  · -- Backward: If divides, then in the set.
    rintro (h | h | h)
    · -- n = -1
      rw [h]
      norm_num
    · -- n = 0
      rw [h]
      norm_num
    · -- n = 2
      rw [h]
      norm_num