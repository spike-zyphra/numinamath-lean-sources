import Mathlib

/- Compute the sum of all positive integers a≤26 for which there exist integers b and c such that
a+23b+15c−2 and 2a+5b+14c−8 are both multiples of 26 .-/

theorem number_theory_610197: ∑ᶠ a ∈ {a : ℤ | 1 ≤ a ∧ a ≤ 26 ∧ (∃ b c : ℤ,
    (a + 23 * b + 15 * c - 2) % 26 = 0 ∧
    (2 * a + 5 * b + 14 * c - 8) % 26 = 0)}, a = 31 := by
  have valid_a_values : {a : ℤ | 1 ≤ a ∧ a ≤ 26 ∧(∃ b c : ℤ,
    (a + 23 * b + 15 * c - 2) % 26 = 0 ∧
    (2 * a + 5 * b + 14 * c - 8) % 26 = 0)} = {9, 22} := by  -- solve for the set of a's --
    ext a
    constructor
    · intro h
      rcases h with ⟨ha1, ha2, hcond⟩
      rcases hcond with ⟨b, c, h1, h2⟩
      have o: (a - 13 * c + 4) % 26 = 0 := by -- key result for solving the problem --
         have h11: 26 ∣ a + 23 * b + 15 * c - 2 := by
          apply Int.dvd_of_emod_eq_zero at h1
          exact h1
         have h22: 26 ∣ 2 * a + 5 * b + 14 * c - 8 := by
          apply Int.dvd_of_emod_eq_zero at h2
          exact h2
         replace h11: 26 ∣ 5 * a + 115 * b + 75 * c - 10 := by
          rw [show 5 * a + 115 * b + 75 * c - 10 = 5 * (a + 23 * b + 15 * c - 2) by ring]
          omega
         replace h22: 26 ∣ 46 * a + 115 * b + 322 * c - 184 := by
          rw [show 46 * a + 115 * b + 322 * c - 184 = 23 * (2 * a + 5 * b + 14 * c - 8) by ring]
          omega
         have l: 26 ∣ 41 * a + 247 * c -174 := by omega
         rw [show 41 * a + 247 * c -174 = (15 * a + 13 * c + 8) + 26 * (a + 9 * c - 7) by ring] at l
         replace l: 26 ∣ 15 * a + 13 * c + 8 := by omega
         replace l: 26 ∣ 105 * a + 91 * c + 56 := by omega
         rw [show 105 * a + 91 * c + 56 = (a - 13 * c + 4) + 26 * (4 * a + 4 * c + 2) by ring] at l
         omega
      by_cases r: 2 ∣ c
      . apply exists_eq_mul_right_of_dvd at r
        obtain ⟨k, hk⟩ := r
        rw [hk] at o
        rw [show 13 * (2 * k) = 26 * k  by ring] at o
        apply Int.dvd_of_emod_eq_zero at o
        rw [show a - 26 * k + 4 = (a + 4) + 26 * (-k) by ring] at o
        have i: 26 ∣ a + 4 := by
          omega
        have ha: a = 22 := by omega
        simp
        omega
      . replace r: 2 ∣ c + 1 := by omega
        apply exists_eq_mul_right_of_dvd at r
        obtain ⟨k, hk⟩ := r
        replace hk: c = 2 * k - 1 := by omega
        rw [hk] at o
        simp at o
        rw [show a - 13 * (2 * k - 1) + 4 = (a + 17) + 26 * (-k) by ring] at o
        have i: 26 ∣ a + 17 := by
          omega
        replace i: a = 9 := by omega
        simp
        omega
    · intro h
      cases h with
      | inl h =>
        -- Show `a = 9` satisfies the condition
        refine ⟨by linarith, by linarith, ?_⟩
        use 6, -1  -- Example values for `b` and `c`
        rw [h]
        norm_num
      | inr h =>
        -- Show `a = 22` satisfies the condition
        simp at h
        simp
        constructor
        . linarith
        . rw [h]
          simp
          use -2
          use 0
          norm_num
  have eq: (∑ᶠ a ∈ {a : ℤ | 1 ≤ a ∧ a ≤ 26 ∧ (∃ b c : ℤ,
    (a + 23 * b + 15 * c - 2) % 26 = 0 ∧
    (2 * a + 5 * b + 14 * c - 8) % 26 = 0)},a) = (∑ a ∈ {9, 22}, a) := by
    rw [finsum_mem_eq_sum_of_inter_support_eq]
    rw [valid_a_values]
    simp
  rw [eq]
  norm_num