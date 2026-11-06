import Mathlib

theorem number_theory_139021 (n : ℤ) : n - 1 ∣ n ^ 2 + 2 ↔ n = -2 ∨ n = 0 ∨ n = 2 ∨ n = 4 := by
  constructor
  · -- Forward: if n - 1 divides n^2 + 2, then n ∈ {-2,0,2,4}
    intro h
    have h1 : n - 1 ∣ n ^ 2 + 2 := h
    have h2 : n - 1 ∣ 3 := by
      have h3 : n - 1 ∣ n ^ 2 + 2 := h1
      have h4 : n - 1 ∣ (n - 1) * (n + 1) := by
        use n + 1
        all_goals ring_nf
      have h5 : n - 1 ∣ (n ^ 2 + 2 - (n - 1) * (n + 1)) := by
        apply Dvd.dvd.sub
        · exact h3
        · exact h4
      have h6 : n ^ 2 + 2 - (n - 1) * (n + 1) = 3 := by
        ring_nf
      rw [h6] at h5
      exact h5
    have h3 : n - 1 ∣ 3 := h2
    have h4 : n - 1 ≤ 3 := by
      apply Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) h3
    have h5 : n - 1 ≥ -3 := by
      have h6 : -(n - 1) ∣ 3 := by
        exact Int.neg_dvd.2 h3
      have h7 : -(n - 1) ≤ 3 := by
        apply Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) h6
      linarith
    have h6 : n - 1 = -3 ∨ n - 1 = -1 ∨ n - 1 = 1 ∨ n - 1 = 3 := by
      interval_cases h7 : n - 1 <;> try { tauto }
      <;> norm_num at h3 h4 h5 h7 ⊢ <;> tauto
    rcases h6 with (h6 | h6 | h6 | h6)
    · -- n - 1 = -3, so n = -2
      have hn : n = -2 := by
        omega
      simp [hn]
    · -- n - 1 = -1, so n = 0
      have hn : n = 0 := by
        omega
      simp [hn]
    · -- n - 1 = 1, so n = 2
      have hn : n = 2 := by
        omega
      simp [hn]
    · -- n - 1 = 3, so n = 4
      have hn : n = 4 := by
        omega
      simp [hn]
  · -- Backward: if n ∈ { -2,0,2,4 }, then n - 1 divides n^2 + 2
    rintro (hn | hn | hn | hn)
    · -- n = -2
      rw [hn]
      norm_num
    · -- n = 0
      rw [hn]
      norm_num
    · -- n = 2
      rw [hn]
      norm_num
    · -- n = 4
      rw [hn]
      norm_num