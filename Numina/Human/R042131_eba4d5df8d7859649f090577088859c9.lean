import Mathlib

theorem algebra_96609 (n : ℕ) (h : n = 2) :
    IsLeast {k | ∃ m, m > 500 ∧ n ^ 2 ^ k = m} 4 := by 
  rw [h]
  constructor
  · -- $4 \in \{k|\exists m, m > 500 \and 2 ^ 2 ^ k = m\}$
    use 65536
    simp
  · intro k hk
    rcases hk with ⟨m, hm, h2⟩
    by_contra h
    push_neg at h
    interval_cases k <;> norm_num at h2 <;> omega