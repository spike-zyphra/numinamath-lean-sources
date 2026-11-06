import Mathlib

theorem algebra_96653 {M N : ℝ} (hMN : 3/5 = M/45 ∧ M/45 = 60/N) : M + N = 127 := by
  rcases hMN with ⟨h1, h2⟩
  have hM : M = 27 := by
    field_simp at h1
    linarith
  have hN : N = 100 := by
    rw [hM] at h2
    have h4 : N ≠ 0 := by
      by_contra h
      rw [h] at h2
      norm_num at h2
    field_simp [h4] at h2
    linarith
  rw [hM, hN]
  all_goals norm_num