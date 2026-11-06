import Mathlib

theorem number_theory_7779 :
    {(x, y) : ℤ × ℤ | x * y - 10 * (x + y) = 1} =
    {(11, 111), (111, 11), (9, -91), (-91, 9)} := by 
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y) satisfies the equation; prove it's one of the listed solutions
    intro h
    have h1 : x * y - 10 * (x + y) = 1 := h
    have h2 : (x - 10) * (y - 10) = 101 := by
      nlinarith
    have h4 : (x - 10) ∣ 101 := by 
      use (y - 10)
      linarith
    have h5 : (x - 10) = 1 ∨ (x - 10) = 101 ∨ (x - 10) = -1 ∨ (x - 10) = -101 := by
      have h6 : (x - 10) ∣ 101 := h4
      have h7 : (x - 10) ≥ -101 := by
        have h8 : -(x - 10) ∣ 101 := by
          exact Int.neg_dvd.2 h6
        have h9 : -(x - 10) ≤ 101 := by
          apply Int.le_of_dvd (by norm_num) h8
        linarith
      have h10 : (x - 10) ≤ 101 := by 
        apply Int.le_of_dvd (by norm_num) h6
      interval_cases (x - 10) <;> omega
    rcases h5 with h5 | h5 | h5 | h5
    · -- Case where x - 10 = 1
      have hx : x = 11 := by 
        linarith
      have hy : y = 111 := by
        rw [show (x - 10) = 1 by linarith [h5]] at h2
        linarith
      left
      exact ⟨hx, hy⟩
    · -- Case where x - 10 = 101
      have hx : x = 111 := by 
        linarith
      have hy : y = 11 := by 
        rw [show (x - 10) = 101 by linarith [h5]] at h2
        linarith
      right
      left
      exact ⟨hx, hy⟩
    · -- Case where x - 10 = -1
      have hx : x = 9 := by 
        linarith
      have hy : y = -91 := by 
        rw [show (x - 10) = -1 by linarith [h5]] at h2
        linarith
      right
      right
      left
      exact ⟨hx, hy⟩
    · -- Case where x - 10 = -101
      have hx : x = -91 := by 
        linarith
      have hy : y = 9 := by 
        rw [show (x - 10) = -101 by linarith [h5]] at h2
        linarith
      right
      right
      right
      exact ⟨hx, hy⟩
  · -- Show that these four solutions satisfy the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Verify (11, 111) satisfies the equation
      norm_num
    · -- Verify (111, 11) satisfies the equation
      norm_num
    · -- Verify (9, -91) satisfies the equation
      norm_num
    · -- Verify (-91, 9) satisfies the equation
      norm_num