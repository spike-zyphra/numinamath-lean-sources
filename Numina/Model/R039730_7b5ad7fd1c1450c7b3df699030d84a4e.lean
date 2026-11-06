import Mathlib

theorem number_theory_17045 : {n : ℕ | n > 1 ∧ (Nat.digits n 555).length = 4 ∧ ∃ A B, A ≠ B ∧ (Nat.digits n 555) = [B, A, B, A]} = {6} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume $n$ is in the left side set, prove $n = 6$.
    intro h
    rcases h with ⟨hn1, hn2, A, B, hab, hneq⟩
    have h1 : n ≤ 555 := by
      by_contra h
      push_neg at h
      have h2 : (Nat.digits n 555).length = 1 := by
        simp [h]
      rw [h2] at hn2
      all_goals omega
    interval_cases n <;> norm_num at hneq hn2 <;> try { 
      omega 
    } <;> try { 
      simp_all 
      <;> try { 
        tauto 
      } 
    }
  · -- Assume $n = 6$, prove $n$ is in the left side set.
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · native_decide
    · -- Show details of A and B
      refine ⟨2, 3, by norm_num, by native_decide⟩