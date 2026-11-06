import Mathlib

theorem algebra240229 :
    {(x, y) : ℝ × ℝ | (y ≠ 0 ∧ x - y = x * y ∧ x - y= x / y )∨ (y ≠ 0 ∧ x + y = x * y ∧ x + y = x / y)} = {(1 / 2, -1), (- (1 / 2), -1)} := by 
  ext  ⟨x, y⟩  -- Consider an arbitrary pair (x, y)
  constructor
  · intro h
    simp at h
    -- discuss by the two possible cases
    obtain h | h := h
    -- cases 1 : x - y = x * y ∧ x - y = x / y
    obtain ⟨hy, h1, h2⟩ := h
    have eq1 : x * (y - 1) * (y + 1) = 0 := by 
      have aux : x * y = x / y := by 
        linarith
      field_simp at aux
      linarith
    have eq2 : x = 0 ∨ y - 1= 0 ∨ y + 1 = 0:= by
      have xeq : x * (y ^ 2 - 1) = 0 := by 
        linarith
      have xeq1 : x = 0 ∨ y ^ 2 - 1 = 0 := by
        exact mul_eq_zero.mp xeq
      obtain xeq1 | xeq2 := xeq1
      left 
      exact xeq1
      have yeq : y ^ 2 - 1= (y - 1) * (y + 1) := by ring
      right
      rw [xeq2] at yeq
      exact mul_eq_zero.mp (id (Eq.symm yeq))
    -- by_cases x = 0, y=1 , y = -1
    rcases eq2 with xeq | heq | heq
    have yeq : y = 0 := by 
      rw [xeq] at h1
      linarith
    by_contra hc
    exact hy yeq
    have yeq : y = 1 := by linarith
    rw [yeq] at h1
    simp at h1
    have yeq : y = -1 := by linarith
    rw [yeq] at h1
    have xeq : x = - (1/2) := by linarith
    rw [xeq, yeq]
    simp
    -- cases 2 : y ≠ 0 ∧ x + y = x * y ∧ x + y = x / y)
    obtain ⟨hy, h1, h2⟩ := h
    have eq1 : x * (y - 1) * (y + 1) = 0 := by 
      have aux : x * y = x / y := by 
        linarith
      field_simp at aux
      linarith
    have eq2 : x = 0 ∨ y - 1= 0 ∨ y + 1 = 0:= by
      have xeq : x * (y ^ 2 - 1) = 0 := by 
        linarith
      have xeq1 : x = 0 ∨ y ^ 2 - 1 = 0 := by
        exact mul_eq_zero.mp xeq
      obtain xeq1 | xeq2 := xeq1
      left 
      exact xeq1
      have yeq : y ^ 2 - 1= (y - 1) * (y + 1) := by ring
      right
      rw [xeq2] at yeq
      exact mul_eq_zero.mp (id (Eq.symm yeq))
    -- by_cases x = 0, y=1 , y = -1
    rcases eq2 with xeq | heq | heq
    have yeq : y = 0 := by 
      rw [xeq] at h1
      linarith
    -- by_cases x = 0, y=1 , y = -1
    by_contra hc
    exact hy yeq
    have yeq : y = 1 := by linarith
    rw [yeq] at h1
    simp at h1
    have yeq : y = -1 := by linarith
    rw [yeq] at h1
    simp at h1
    have xeq : x = 1 / 2 := by linarith
    rw [yeq, xeq]
    simp
  intro h
  simp at h
  obtain h | h := h
  obtain ⟨xeq, yeq⟩ := h
  simp
  right
  rw [xeq, yeq]
  constructor
  simp
  constructor
  norm_num
  linarith
  simp
  left
  obtain ⟨xeq, yeq⟩ := h
  rw [xeq, yeq]
  constructor
  simp
  constructor
  norm_num
  linarith