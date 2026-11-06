import Mathlib

theorem algebra_236125 (m n : ℤ) : m * n + 5 * m + 2 * n = 121 ↔
    (m = -1 ∧ n = 126) ∨ (m = -3 ∧ n = -136) ∨ (m = 129 ∧ n = -4) ∨ (m = -133 ∧ n = -6) := by
  constructor
  · -- Forward direction: if equation holds, then (m, n) is one of the four pairs
    intro h
    have h1 : m * n + 5 * m + 2 * n = 121 := h
    have h2 : (m + 2) * (n + 5) = 131 := by
      linarith [h1]
    have h3 : (m + 2) ∣ 131 := by
      use (n + 5)
      linarith
    have h4 : (m + 2) = 1 ∨ (m + 2) = 131 ∨ (m + 2) = -1 ∨ (m + 2) = -131 := by
      have h4 : (m + 2) ≤ 131 := by
        apply Int.le_of_dvd (by norm_num) h3
      have h5 : (m + 2) ≥ -131 := by
        have h6 : -(m + 2) ∣ 131 := by 
          exact Int.neg_dvd.2 h3
        have h7 : -(m + 2) ≤ 131 := by
          apply Int.le_of_dvd (by norm_num) h6
        linarith
      interval_cases k : (m + 2) <;> omega
    rcases h4 with h4 | h4 | h4 | h4
    · -- Case (m + 2) = 1
      have h5 : (n + 5) = 131 := by
        rw [h4] at h2
        linarith
      have hm : m = -1 := by linarith
      have hn : n = 126 := by linarith
      left
      exact ⟨hm, hn⟩
    · -- Case (m + 2) = 131
      have h5 : (n + 5) = 1 := by
        rw [h4] at h2
        linarith
      have hm : m = 129 := by linarith
      have hn : n = -4 := by linarith
      right
      right
      left
      exact ⟨hm, hn⟩
    · -- Case (m + 2) = -1
      have h5 : (n + 5) = -131 := by
        rw [h4] at h2
        linarith
      have hm : m = -3 := by linarith
      have hn : n = -136 := by linarith
      right
      left
      exact ⟨hm, hn⟩
    · -- Case (m + 2) = -131
      have h5 : (n + 5) = -1 := by
        rw [h4] at h2
        linarith
      have hm : m = -133 := by linarith
      have hn : n = -6 := by linarith
      right
      right
      right
      exact ⟨hm, hn⟩
  · -- Backward direction: each of the four pairs satisfies the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (-1, 126)
      norm_num
    · -- (-3, -136)
      norm_num
    · -- (129, -4)
      norm_num
    · -- (-133, -6)
      norm_num