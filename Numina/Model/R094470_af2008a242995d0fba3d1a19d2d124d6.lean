import Mathlib

theorem algebra_103698 (x y : ℤ) : 2*(x^2+y^2)=5*(x*y+1) ↔ (x=-1 ∧ y=-3) ∨ (x=3 ∧ y=1) ∨ (x=1 ∧ y=3) ∨ (x=-3 ∧ y=-1) := by
  constructor
  · -- Assume 2*(x^2+y^2)=5*(x*y+1), prove (x=-1 ∧ y=-3) ∨ (x=3 ∧ y=1) ∨ (x=1 ∧ y=3) ∨ (x=-3 ∧ y=-1)
    intro h
    have h1 : 2 * x^2 + 2 * y^2 = 5 * (x * y + 1) := by linarith
    have h2 : (2 * x - y) * (x - 2 * y) = 5 := by 
      nlinarith 
    have h3 : (2 * x - y) * (x - 2 * y) = 5 := h2
    have h4 : (2 * x - y) ∣ 5 := by 
      use (x - 2 * y)
      linarith
    have h5 : (2 * x - y) = 1 ∨ (2 * x - y) = 5 ∨ (2 * x - y) = -1 ∨ (2 * x - y) = -5 := by 
      have h6 : (2 * x - y) ∣ 5 := h4
      have h7 : (2 * x - y) ≤ 5 := by 
        exact Int.le_of_dvd (by norm_num) h6
      have h8 : (2 * x - y) ≥ -5 := by 
        have h9 : -(2 * x - y) ∣ 5 := by 
          exact Int.neg_dvd.2 h6
        have h10 : -(2 * x - y) ≤ 5 := by 
          exact Int.le_of_dvd (by norm_num) h9
        linarith
      interval_cases (2 * x - y) <;> tauto
    rcases h5 with h5 | h5 | h5 | h5
    · -- Case where 2x - y = 1, then x - 2y = 5
      have h6 : x - 2 * y = 5 := by 
        rw [h5] at h2
        linarith
      have hy : y = -3 := by 
        linarith [h5, h6]
      have hx : x = -1 := by 
        linarith [h5, hy]
      left
      exact ⟨hx, hy⟩
    · -- Case where 2x - y = 5, then x - 2y = 1
      have h6 : x - 2 * y = 1 := by 
        rw [h5] at h2
        linarith
      have hy : y = 1 := by 
        linarith [h5, h6]
      have hx : x = 3 := by 
        linarith [h5, hy]
      right
      left
      exact ⟨hx, hy⟩
    · -- Case where 2x - y = -1, then x - 2y = -5
      have h6 : x - 2 * y = -5 := by 
        rw [h5] at h2
        linarith
      have hy : y = 3 := by 
        linarith [h5, h6]
      have hx : x = 1 := by 
        linarith [h5, hy]
      right
      right
      left
      exact ⟨hx, hy⟩
    · -- Case where 2x - y = -5, then x - 2y = -1
      have h6 : x - 2 * y = -1 := by 
        rw [h5] at h2
        linarith
      have hy : y = -1 := by 
        linarith [h5, h6]
      have hx : x = -3 := by 
        linarith [h5, hy]
      right
      right
      right
      exact ⟨hx, hy⟩
  · -- Assume (x,y) is one of (-1,-3),(3,1),(1,3),(-3,-1) then 2*(x^2+y^2)=5*(x*y+1)
    rintro (h | h | h | h)
    · -- First case: (-1,-3)
      rw [h.1, h.2]
      norm_num
    · -- Second case: (3,1)
      rw [h.1, h.2]
      norm_num
    · -- Third case: (1,3)
      rw [h.1, h.2]
      norm_num
    · -- Fourth case: (-3,-1)
      rw [h.1, h.2]
      norm_num