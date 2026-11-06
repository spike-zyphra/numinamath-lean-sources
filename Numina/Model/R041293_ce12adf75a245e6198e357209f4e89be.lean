import Mathlib

theorem algebra_22663 : IsLeast {x : ℤ | ∃ m n, x = |m - n| ∧ 3 * m + 4 * n = 100} 3 := by
  constructor
  · -- Show that 3 is in the set
    use 16, 13
    all_goals norm_num
  · -- Show that no integer less than 3 is in the set
    intro x hx
    rcases hx with ⟨m, n, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : |m - n| < 3 := by 
      omega 
    have h4 : m - n = -2 ∨ m - n = -1 ∨ m - n = 0 ∨ m - n = 1 ∨ m - n = 2 := by 
      cases' abs_lt.mp h3 with h5 h6 
      omega 
    rcases h4 with (h | h | h | h | h)
    · -- m - n = -2 
      have : n = m + 2 := by linarith
      rw [this] at h2 
      have : 7 * m = 92 := by 
        omega 
      omega 
    · -- m - n = -1 
      have : n = m + 1 := by linarith 
      rw [this] at h2 
      have : 7 * m = 96 := by 
        omega 
      omega 
    · -- m - n = 0 
      have : m = n := by linarith
      rw [this] at h2 
      have : 7 * n = 100 := by 
        omega 
      omega 
    · -- m - n = 1 
      have : m = n + 1 := by linarith
      rw [this] at h2 
      have : 7 * n = 97 := by 
        omega 
      omega 
    · -- m - n = 2 
      have : m = n + 2 := by linarith 
      rw [this] at h2 
      have : 7 * n = 94 := by 
        omega 
      omega