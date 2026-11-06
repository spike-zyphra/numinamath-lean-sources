import Mathlib

theorem algebra_125968 :
    IsGreatest {a : ℝ | ∃ x y : ℤ, x - 4 * y = 1 ∧ a * x + 3 * y = 1} 1 := by
  constructor
  · -- Show that 1 is in the set.
    use 1, 0
    norm_num
  · -- Show that 1 is greatest in the set.
    intro a ha
    rcases ha with ⟨x, y, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : (x : ℝ) - 4 * (y : ℝ) = (1 : ℝ) := by 
      exact_mod_cast h1
    have h4 : a * (x : ℝ) + 3 * (y : ℝ) = (1 : ℝ) := by
      exact_mod_cast h2
    have eq1 : (x : ℝ) = 1 + 4 * (y : ℝ) := by
      linarith 
    rw [eq1] at h4 
    have eq6 : (a : ℝ) + (y : ℝ) * (4 * a + 3) = (1 : ℝ) := by 
      nlinarith 
    have eq5 : (y : ℝ) * (4 * a + 3) = (1 - a : ℝ) := by 
      nlinarith 
    have h8 : (y : ℝ) = (1 - a) / (4 * a + 3) := by
      have h' : (4 * a + 3) ≠ 0 := by
        by_contra h'
        have : a = -3/4 := by nlinarith 
        linarith 
      field_simp [h']
      linarith 
    have h8' : (y : ℤ) = (1 - a) / (4 * a + 3) := by
      exact_mod_cast h8 
    have h9 : (y : ℝ) = (y : ℤ) := by 
      simp 
    have h12 : (y : ℤ) ≤ 0 := by
      by_contra h' 
      push_neg at h' 
      have h3 : y ≥ 1 := by
        omega 
      have h5 : (y : ℝ) ≥ (1 : ℝ) := by 
        exact_mod_cast h3 
      nlinarith 
    have h8' : (y : ℤ) ≥ -1 := by 
      by_contra h' 
      push_neg at h' 
      have h'2 : y ≤ -2 := by 
        omega 
      have h'5 : (y : ℝ) ≤ (-2 : ℝ) := by 
        exact_mod_cast h'2 
      nlinarith 
    have hy0 : y = 0 ∨ y = -1 := by 
      omega 
    rcases hy0 with (hy | hy)
    · -- Case y = 0
      have hy0' : (y : ℝ) = 0 := by 
        exact_mod_cast hy 
      have eq7 : (a : ℝ) = 1 := by 
        rw [hy0'] at eq6 
        nlinarith 
      nlinarith 
    · -- Case y = -1
      have hy1' : (y : ℝ) = -1 := by 
        exact_mod_cast hy 
      rw [hy1'] at eq6 
      nlinarith