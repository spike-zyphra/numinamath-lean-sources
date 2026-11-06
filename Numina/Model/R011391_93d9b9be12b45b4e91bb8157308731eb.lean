import Mathlib

theorem number_theory_622830 :
    IsLeast {x : ℕ | x > 0 ∧ (∃ n : ℕ, n^2 = x^2 + 3072) ∧ 4 ∣ x} 8 := by
  constructor
  · -- First, we verify that 8 is in the set.
    constructor
    · norm_num
    constructor
    · use 56
      all_goals norm_num
    · norm_num
  · -- Now, we need to show there's no smaller element in the set.
    intro y hy
    rcases hy with ⟨hy_pos, ⟨n, hn⟩, hy_div⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 56 := by
      nlinarith
    have h4 : y = 4 := by
      omega
    rw [h4] at hn
    have h2 : n > 0 := by
      have h1 : n ^ 2 = 4 ^ 2 + 3072 := by
        linarith
      have h3 : n > 0 := by
        by_contra h
        push_neg at h
        have : n = 0 := by
          omega
        rw [this] at h1
        omega
      exact h3
    have h5 : n ≤ 56 := by
      nlinarith
    interval_cases n <;> try { norm_num at hn <;> tauto }