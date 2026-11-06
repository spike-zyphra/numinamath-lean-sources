import Mathlib

theorem algebra_191374 (x y : ℤ) : 2 * x + 5 * y = x * y - 1 ↔
    (x = 6 ∧ y = 13) ∨ (x = 16 ∧ y = 3) ∨ (x = 4 ∧ y = -9) ∨ (x = -6 ∧ y = 1) := by
  constructor
  · -- Forward direction: Equation implies solutions
    intro h
    have h1 : x * y - 2 * x - 5 * y = 1 := by linarith
    have h2 : (x - 5) * (y - 2) = 11 := by
      nlinarith
    have h3 : (x - 5) = 1 ∨ (x - 5) = 11 ∨ (x - 5) = -1 ∨ (x - 5) = -11 := by
      have h4 : (x - 5) ∣ 11 := by
        use (y - 2)
        linarith
      have h7 : (x - 5) = 1 ∨ (x - 5) = 11 ∨ (x - 5) = -1 ∨ (x - 5) = -11 := by
        have h8 : (x - 5) ∣ 11 := h4
        have h11 : (x - 5) ≤ 11 := by
          apply Int.le_of_dvd (by norm_num) h8
        have h12 : (x - 5) ≥ -11 := by
          have h13 : (- (x - 5) : ℤ) ∣ 11 := by
            exact Int.neg_dvd.2 h8
          have h14 : (- (x - 5) : ℤ) ≤ 11 := by 
            apply Int.le_of_dvd (by norm_num) h13
          linarith
        interval_cases h15 : (x - 5) <;> omega
      exact h7
    rcases h3 with h4 | h4 | h4 | h4
    · -- Case \(x - 5 = 1\): Then \(y - 2 = 11\), so \(x = 6\), \(y = 13\)
      have hx : x = 6 := by linarith
      have hy : y = 13 := by
        have : (y - 2) = 11 := by
          rw [h4] at h2
          nlinarith
        linarith
      left
      exact ⟨hx, hy⟩
    · -- Case \(x - 5 = 11\): Then \(y - 2 = 1\), so \(x = 16\), \(y = 3\)
      have hx : x = 16 := by linarith
      have hy : y = 3 := by
        have : (y - 2) = 1 := by
          rw [h4] at h2
          nlinarith
        linarith
      right
      left
      exact ⟨hx, hy⟩
    · -- Case \(x - 5 = -1\): Then \(y - 2 = -11\), so \(x = 4\), \(y = -9\)
      have hx : x = 4 := by linarith
      have hy : y = -9 := by
        have : (y - 2) = -11 := by
          rw [h4] at h2
          nlinarith
        linarith
      right
      right
      left
      exact ⟨hx, hy⟩
    · -- Case \(x - 5 = -11\): Then \(y - 2 = -1\), so \(x = -6\), \(y = 1\)
      have hx : x = -6 := by linarith
      have hy : y = 1 := by
        have : (y - 2) = -1 := by
          rw [h4] at h2
          nlinarith
        linarith
      right
      right
      right
      exact ⟨hx, hy⟩
  · -- Backward direction: Solutions satisfy equation
    rintro (h | h | h | h)
    · -- Check \( (6, 13) \)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Check \( (16, 3) \)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Check \( (4, -9) \)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Check \( (-6, 1) \)
      rcases h with ⟨rfl, rfl⟩
      norm_num