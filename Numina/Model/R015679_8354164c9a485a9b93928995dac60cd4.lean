import Mathlib

def S (k : ℕ) := fun n => k + (n - 1) * k ^ 2

theorem number_theory_212928 :
    ∑ᶠ k ∈ {k | ∃ n, S k n = 306}, k = 326 := by
  have h1 : {k | ∃ n, S k n = 306} = {1, 2, 17, 306} := by
    ext k
    simp [S]
    constructor
    · -- Suppose that ∃ n, S k n = 306, we need to show k ∈ {1, 2, 17, 306}
      rintro ⟨n, hn⟩
      have h_pos1 : k ≤ 306 := by
        by_contra h
        push_neg at h
        have h2 : k > 306 := by linarith
        nlinarith [hn, h2, sq_pos_of_pos (show 0 < (k: ℕ) by nlinarith), sq_pos_of_pos (show 0 < (n: ℕ) by nlinarith)]
      interval_cases k <;> omega
    · -- Show that k ∈ {1, 2, 17, 306} implies ∃ n, S k n = 306
      rintro (rfl | rfl | rfl | rfl)
      · -- k = 1
        use 306
        all_goals norm_num [S]
      · -- k = 2
        use 77
        all_goals norm_num [S]
      · -- k = 17
        use 2
        all_goals norm_num [S]
      · -- k = 306
        use 1
        all_goals norm_num [S]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp