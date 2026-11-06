import Mathlib

theorem number_theory_134510 (m n : ℤ) :
    m^2 - 2 * m * n - 3 * n^2 = 5 ↔ (m = 4 ∧ n = 1) ∨ (m = -4 ∧ n = -1) ∨
    (m = 2 ∧ n = -1) ∨ (m = -2 ∧ n = 1) := by
  constructor
  · -- Assume that $m^2 - 2mn - 3n^2 = 5$, we need to find the integer solutions
    intro h
    have h₁ : (m - 3 * n) * (m + n) = 5 := by
      nlinarith
    have h₂ : (m - 3 * n) = 1 ∨ (m - 3 * n) = 5 ∨ (m - 3 * n) = -1 ∨ (m - 3 * n) = -5 := by
      have h₁' : (m - 3 * n) * (m + n) = 5 := h₁
      have h₂ : (m - 3 * n) ∣ 5 := by
        use (m + n)
        linarith
      have h₃ : (m - 3 * n) ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h₂
      have h₄ : (m - 3 * n) ≥ -5 := by
        have h₅ : -(m - 3 * n) ∣ 5 := by
          exact Int.neg_dvd.2 h₂
        have h₆ : -(m - 3 * n) ≤ 5 := by
          apply Int.le_of_dvd (by norm_num) h₅
        linarith
      interval_cases (m - 3 * n) <;> omega
    rcases h₂ with h₂ | h₂ | h₂ | h₂
    · -- Case where m - 3n = 1, so m + n = 5
      have h₃ : m + n = 5 := by
        nlinarith
      have hn : n = 1 := by
        omega
      have hm : m = 4 := by
        omega
      simp [hm, hn]
      <;> omega
    · -- Case where m - 3n = 5, so m + n = 1
      have h₃ : m + n = 1 := by
        nlinarith
      have hn : n = -1 := by
        omega
      have hm : m = 2 := by
        omega
      simp [hm, hn]
      <;> omega
    · -- Case where m - 3n = -1, so m + n = -5
      have h₃ : m + n = -5 := by
        nlinarith
      have hn : n = -1 := by
        omega
      have hm : m = -4 := by
        omega
      simp [hm, hn]
      <;> omega
    · -- Case where m - 3n = -5, so m + n = -1
      have h₃ : m + n = -1 := by
        nlinarith
      have hn : n = 1 := by
        omega
      have hm : m = -2 := by
        omega
      simp [hm, hn]
      <;> omega
  · -- Conversely, assume that (m, n) is one of the four given solutions
    rintro (h | h | h | h)
    · -- Case where (m, n) = (4, 1)
      rw [h.1, h.2]
      norm_num
    · -- Case where (m, n) = (-4, -1)
      rw [h.1, h.2]
      norm_num
    · -- Case where (m, n) = (2, -1)
      rw [h.1, h.2]
      norm_num
    · -- Case where (m, n) = (-2, 1)
      rw [h.1, h.2]
      norm_num