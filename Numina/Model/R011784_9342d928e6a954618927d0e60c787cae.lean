import Mathlib

theorem number_theory_157346 :
    {n : ℕ | n + (Nat.digits 10 n).sum = 1981} = {1958} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h: n + (Nat.digits 10 n).sum = 1981, prove n = 1958
    intro h
    have h1 : n ≤ 1981 := by 
      omega
    have h2 : n ≥ 1954 := by 
      by_contra h3 
      push_neg at h3 
      have h4 : n ≤ 1953 := by 
        omega 
      interval_cases n <;> norm_num at h ⊢ <;> omega 
    interval_cases n <;> norm_num at h ⊢ 
    <;> omega 
  · -- Assume n = 1958 
    intro h 
    rw [h] 
    all_goals 
      norm_num