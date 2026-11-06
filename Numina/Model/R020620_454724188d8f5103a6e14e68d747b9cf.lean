import Mathlib

theorem number_theory_140106 :
    Set.ncard {n : ℕ | n.Prime ∧ n = 11 ∨ n.Prime ∧ n = 12 ∨ n.Prime ∧ n = 13 ∨
      n.Prime ∧ n = 14 ∨ n.Prime ∧ n = 15 ∨ n.Prime ∧ n = 16 ∨ n.Prime ∧ n = 17} = 3 := by
  have h1 : {n : ℕ | n.Prime ∧ n = 11 ∨ n.Prime ∧ n = 12 ∨ n.Prime ∧ n = 13 ∨
      n.Prime ∧ n = 14 ∨ n.Prime ∧ n = 15 ∨ n.Prime ∧ n = 16 ∨ n.Prime ∧ n = 17} = {11, 13, 17} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h
      intro h
      rcases h with (h | h | h | h | h | h | h)
      · -- Case 1: n.Prime ∧ n = 11
        rcases h with ⟨h_prime, hn⟩
        rw [hn]
        tauto
      · -- Case 2: n.Prime ∧ n = 12
        rcases h with ⟨h_prime, hn⟩
        rw [hn] at h_prime
        norm_num at h_prime
      · -- Case 3: n.Prime ∧ n = 13
        rcases h with ⟨h_prime, hn⟩
        rw [hn]
        tauto
      · -- Case 4: n.Prime ∧ n = 14
        rcases h with ⟨h_prime, hn⟩
        rw [hn] at h_prime
        norm_num at h_prime
      · -- Case 5: n.Prime ∧ n = 15
        rcases h with ⟨h_prime, hn⟩
        rw [hn] at h_prime
        norm_num at h_prime
      · -- Case 6: n.Prime ∧ n = 16
        rcases h with ⟨h_prime, hn⟩
        rw [hn] at h_prime
        norm_num at h_prime
      · -- Case 7: n.Prime ∧ n = 17
        rcases h with ⟨h_prime, hn⟩
        rw [hn]
        tauto
    · -- Show the reverse direction
      rintro (rfl | rfl | rfl)
      · -- Case 1: n = 11
        norm_num
      · -- Case 2: n = 13
        norm_num
      · -- Case 3: n = 17
        norm_num
  rw [h1]
  norm_num