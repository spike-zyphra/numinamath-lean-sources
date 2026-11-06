import Mathlib

theorem number_theory_98219 :
    Set.ncard {N : ℕ | 0 < N ∧ (36 % (N + 2) = 0)} = 7 := by
  have : {N : ℕ | 0 < N ∧ (36 % (N + 2) = 0)} = {1, 2, 4, 7, 10, 16, 34} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
        Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if N is in our set, it is one of the explicit values
      intro h
      rcases h with ⟨hNpos, hdiv⟩
      have hNle : N ≤ 34 := by
        by_contra h'
        push_neg at h'
        have hNge : N ≥ 35 := by omega
        have : N + 2 ≥ 37 := by omega
        have hrem : 36 % (N + 2) = 36 := by
          rw [Nat.mod_eq_of_lt]
          linarith
          all_goals omega
        rw [hrem] at hdiv
        omega
      interval_cases N <;> norm_num at *
      all_goals omega
    · -- Second direction: each explicit N is in our set
      rintro (r | r | r | r | r | r | r)
      · -- N = 1
        rw [r]
        constructor <;> norm_num
      · -- N = 2
        rw [r]
        constructor <;> norm_num
      · -- N = 4
        rw [r]
        constructor <;> norm_num
      · -- N = 7
        rw [r]
        constructor <;> norm_num
      · -- N = 10
        rw [r]
        constructor <;> norm_num
      · -- N = 16
        rw [r]
        constructor <;> norm_num
      · -- N = 34
        rw [r]
        constructor <;> norm_num
  rw [this]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]