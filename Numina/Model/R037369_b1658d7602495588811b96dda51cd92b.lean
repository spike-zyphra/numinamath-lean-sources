import Mathlib

theorem algebra_322459 {a : ℕ → ℕ}
    (ha0 : a 0 = 1)
    (han : ∀ n ≥ 1, a n = 2 * ∑ i in Finset.Icc 0 (n - 1), a i) :
    IsGreatest {n | 0 < n ∧ a n ≤ 2018} 7 := by
  have ha1 : a 1 = 2 * a 0 := by
    specialize han 1 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0] at ha1
  have ha2 : a 2 = 2 * (a 0 + a 1) := by
    specialize han 2 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1] at ha2
  have ha3 : a 3 = 2 * (a 0 + a 1 + a 2) := by
    specialize han 3 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1, ha2] at ha3
  have ha4 : a 4 = 2 * (a 0 + a 1 + a 2 + a 3) := by
    specialize han 4 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1, ha2, ha3] at ha4
  have ha5 : a 5 = 2 * (a 0 + a 1 + a 2 + a 3 + a 4) := by
    specialize han 5 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1, ha2, ha3, ha4] at ha5
  have ha6 : a 6 = 2 * (a 0 + a 1 + a 2 + a 3 + a 4 + a 5) := by
    specialize han 6 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1, ha2, ha3, ha4, ha5] at ha6
  have ha7 : a 7 = 2 * (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6) := by
    specialize han 7 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1, ha2, ha3, ha4, ha5, ha6] at ha7
  have ha8 : a 8 = 2 * (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7) := by
    specialize han 8 (by norm_num)
    simp [Finset.sum_Icc_succ_top] at han
    all_goals omega
  rw [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7] at ha8
  constructor
  · -- Show 7 ∈ {n | 0 < n ∧ a n ≤ 2018}
    constructor
    · -- Show 7 > 0
      norm_num
    · -- Show a 7 ≤ 2018
      omega
  · -- Show 7 is greatest in {n | 0 < n ∧ a n ≤ 2018}
    intro n hn
    have h2 : 0 < n := by
      simpa using hn.1
    have h3 : a n ≤ 2018 := by
      simpa using hn.2
    by_contra h
    push_neg at h
    have h4 : n ≥ 8 := by
      omega
    -- Show a n >= 4374 for n >= 8
    have h6 : a n ≥ a 8 := by
      have h7 : ∀ k, k ≥ 8 → a k ≥ a 8 := by
        intro k hk
        have h8 : k ≥ 8 := hk
        have base8 : a 8 ≥ a 8 := by omega
        have step10 : ∀ (m : ℕ), m ≥ 8 → a m ≥ a 8 → a (m + 1) ≥ a 8 := by
          intro m hm h
          have eq1 : a (m + 1) = 2 * ∑ i in Finset.Icc 0 m, a i := by
            specialize han (m + 1) (by omega)
            simpa using han
          have h12 : a (m + 1) ≥ a m := by
            have eq2 : a m = 2 * ∑ i in Finset.Icc 0 (m - 1), a i := by
              apply han m
              all_goals omega
            have h11 : ∑ i in Finset.Icc 0 m, a i ≥ ∑ i in Finset.Icc 0 (m - 1), a i := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · -- Show that Icc 0 (m - 1) ⊆ Icc 0 m
                intro i hi
                simp at hi ⊢
                omega
              · -- Show that ∀ i ∈ Icc 0 (m - 1), a i ≤ a i
                intro i hi
                simp
            rw [eq1, eq2]
            omega
          have h13 : a m ≥ a 8 := h
          omega
        exact Nat.le_induction base8 step10 k (by omega)
      specialize h7 n (by omega)
      simpa using h7
    -- Now contradiction
    have h9 : a n ≥ 4374 := by
      omega
    omega