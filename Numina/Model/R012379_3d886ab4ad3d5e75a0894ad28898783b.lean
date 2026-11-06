import Mathlib


theorem number_theory_7066 (s : Finset ℕ) (h : s = {n : ℕ | 4 < n ∧ (2016 % n) = 3}) :
    ∑ n ∈ s, n = 2972 := by
  have h1 : s = {11, 33, 61, 183, 671, 2013} := by
    have h3 : (s : Set ℕ) = {n : ℕ | 4 < n ∧ (2016 % n) = 3} := by
      exact_mod_cast h
    have h5 : {n : ℕ | 4 < n ∧ (2016 % n) = 3} = {11, 33, 61, 183, 671, 2013} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
      constructor
      · -- If 4 < n ∧ 2016 % n = 3 then n ∈ {11, 33, 61, 183, 671, 2013}
        intro h
        rcases h with ⟨h4, h5⟩
        have h6 : n ≤ 2016 := by
          by_contra h
          push_neg at h
          have h7 : 2016 % n = 2016 := by
            rw [Nat.mod_eq_of_lt]
            all_goals linarith
          omega
        interval_cases n <;> norm_num at h4 h5 ⊢
      · -- If n ∈ {11, 33, 61, 183, 671, 2013} then 4 < n ∧ 2016 % n = 3
        rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        all_goals
          constructor <;> norm_num
    have h6 : (s : Set ℕ) = {11, 33, 61, 183, 671, 2013} := by
      rw [h5] at h3
      exact h3
    have h7 : s = ({11, 33, 61, 183, 671, 2013} : Finset ℕ) := by
      have h8 : (s : Set ℕ) = (↑({11, 33, 61, 183, 671, 2013} : Finset ℕ) : Set ℕ) := by
        rw [h6]
        all_goals
          aesop
      have h9 : s = ({11, 33, 61, 183, 671, 2013} : Finset ℕ) := by
        exact_mod_cast h8
      exact h9
    exact h7
  rw [h1]
  native_decide