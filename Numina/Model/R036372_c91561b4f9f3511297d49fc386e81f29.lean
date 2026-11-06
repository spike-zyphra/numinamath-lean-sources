import Mathlib

theorem number_theory_167336 :
    {n : ℕ | n % 2 = 1 ∧ ∃ j : ℕ, j ≤ 9 ∧ j > 0 ∧ n^2 + (n + 2)^2 + (n + 4)^2 = j * 1111} =
    {41} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in left side, need show {41}
    intro h
    rcases h with ⟨h1, ⟨j, ⟨hj1, hj2, heq⟩⟩⟩
    have h2 : n ≤ 57 := by
      by_contra h
      push_neg at h
      have h3 : n ^ 2 + (n + 2) ^ 2 + (n + 4) ^ 2 > 9 * 1111 := by
        nlinarith [h, sq_nonneg (n + 4)]
      have h4 : j ≤ 9 := by linarith
      have h5 : j > 0 := by linarith
      interval_cases j <;> omega
    interval_cases n <;> try { 
      omega 
    } <;> try { 
      interval_cases j <;> omega 
    }
  · -- Assume {41} in left side
    intro h
    rw [h]
    constructor
    · norm_num
    · -- Show that exists j
      use 5
      all_goals norm_num