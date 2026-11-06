import Mathlib

theorem number_theory_3642 :
  ∑ᶠ a ∈ {a | ∃ k : ℕ, 0 < k ∧ Nat.gcd 2017 k = a}, a = 2018 := by
  have h1 : {a | ∃ k : ℕ, 0 < k ∧ Nat.gcd 2017 k = a} = {1, 2017} := by
    ext a 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume $a$ is in the left side set, then it must be either $1$ or $2017$.
      rintro ⟨k, hk, h⟩
      have h2 : a ∣ 2017 := by 
        have h3 : a ∣ Nat.gcd 2017 k := by 
          rw [show Nat.gcd 2017 k = a by omega]
          all_goals simp
        have h4 : Nat.gcd 2017 k ∣ 2017 := by 
          apply Nat.gcd_dvd_left 
        have h5 : a ∣ 2017 := by 
          exact dvd_trans h3 h4 
        assumption 
      have h3 : a ∣ 2017 := h2 
      have h4 : a = 1 ∨ a = 2017 := by 
        have h5 : a ≤ 2017 := by 
          exact Nat.le_of_dvd (by norm_num) h3 
        interval_cases a <;> norm_num at h3 ⊢ 
      tauto 
    · -- Assume $a \in \{1, 2017\}$, then it is in the left side set.
      rintro (rfl | rfl)
      · -- Case $a = 1$.
        refine ⟨1, by norm_num, by norm_num⟩ 
      · -- Case $a = 2017$.
        refine ⟨2017, by norm_num, by norm_num⟩ 
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num