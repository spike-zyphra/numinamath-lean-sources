import Mathlib

theorem number_theory_160864 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ¬∃ n m, n ≥ 0 ∧ m ≥ 0 ∧ x + n = y - m ∨ x - 5 * n = y + 7 * m) :
    ⌊x⌋ + ⌊y⌋ ≤ 4 := by 
  by_contra h1 
  push_neg at h1
  have h4 : ⌊x⌋ + ⌊y⌋ ≥ 5 := by 
    omega 
  have h5 : ∃ n m, n ≥ 0 ∧ m ≥ 0 ∧ x + n = y - m ∨ x - 5 * n = y + 7 * m := by
    by_cases h2 : x ≥ y 
    · -- Case x ≥ y 
      use (x - y) / 5, 0 
      right 
      have hn1 : (x - y) / 5 ≥ 0 := by 
        have hxy : x - y ≥ 0 := by linarith 
        linarith 
      all_goals norm_num at * <;> linarith 
    · -- Case x < y 
      use 0, y - x 
      left 
      have hm1 : y - x ≥ 0 := by 
        linarith 
      constructor 
      · -- n ≥ 0 
        linarith 
      constructor 
      · -- m ≥ 0 
        linarith 
      · -- x + 0 = y - (y - x) 
        linarith 
  contradiction