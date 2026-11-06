import Mathlib

theorem number_theory_3920 :
    ∑ᶠ a ∈ {a : ℤ | a > 0 ∧ ∃ m n, m^2 = a - 52 ∧ n^2 = a + 91}, a = 53 + 5093 := by
  have h1 : {a : ℤ | a > 0 ∧ ∃ m n, m^2 = a - 52 ∧ n^2 = a + 91} = {53, 5093} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume a is a positive integer such that there exist m, n with m^2 = a - 52 and n^2 = a + 91.
      intro h
      rcases h with ⟨ha_pos, m, n, hm, hn⟩
      have h_eq1 : n^2 - m^2 = 143 := by
        nlinarith
      have h_eq2 : (n - m) * (n + m) = 143 := by 
        linarith [h_eq1]
      have h2 : n - m = 1 ∨ n - m = 11 ∨ n - m = 13 ∨ n - m = 143 ∨ n - m = -1 ∨ n - m = -11 ∨ n - m = -13 ∨ n - m = -143 := by
        have h3 : (n - m) ∣ 143 := by
          use (n + m)
          all_goals nlinarith [h_eq2]
        have h4 : (n - m) ∣ 143 := h3
        have h5 : (n - m) ≤ 143 := by
          exact Int.le_of_dvd (by norm_num) h3
        have h6 : (n - m) ≥ -143 := by
          have h7 : -(n - m) ∣ 143 := by 
            exact Int.neg_dvd.2 h3
          have h8 : -(n - m) ≤ 143 := by
            exact Int.le_of_dvd (by norm_num) h7
          linarith
        interval_cases h : (n - m) <;> tauto
      rcases h2 with h | h | h | h | h | h | h | h
      · -- n - m = 1
        have h7 : n + m = 143 := by
          nlinarith
        have h8 : n = 72 := by
          omega
        have h9 : m = 71 := by
          omega
        have ha1 : a = 5093 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = 11
        have h7 : n + m = 13 := by
          nlinarith
        have h8 : n = 12 := by
          omega
        have h9 : m = 1 := by
          omega
        have ha1 : a = 53 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = 13
        have h7 : n + m = 11 := by
          nlinarith
        have h8 : n = 12 := by
          omega
        have h9 : m = -1 := by
          omega
        have ha1 : a = 53 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = 143
        have h7 : n + m = 1 := by
          nlinarith
        have h8 : n = 72 := by
          omega
        have h9 : m = -71 := by
          omega
        have ha1 : a = 5093 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = -1
        have h7 : n + m = -143 := by
          nlinarith
        have h8 : n = -72 := by
          omega
        have h9 : m = -71 := by
          omega
        have ha1 : a = 5093 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = -11
        have h7 : n + m = -13 := by
          nlinarith
        have h8 : n = -12 := by
          omega
        have h9 : m = -1 := by
          omega
        have ha1 : a = 53 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = -13
        have h7 : n + m = -11 := by
          nlinarith
        have h8 : n = -12 := by
          omega
        have h9 : m = 1 := by
          omega
        have ha1 : a = 53 := by
          nlinarith [hm, h9]
        omega
      · -- n - m = -143
        have h7 : n + m = -1 := by
          nlinarith
        have h8 : n = -72 := by
          omega
        have h9 : m = 71 := by
          omega
        have ha1 : a = 5093 := by
          nlinarith [hm, h9]
        omega
    · -- Assume a = 53 or 5093, prove the condition.
      rintro (rfl | rfl)
      · -- a = 53
        constructor
        · norm_num
        · use 1, 12
          all_goals norm_num
      · -- a = 5093
        constructor
        · norm_num
        · use 71, 72
          all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num