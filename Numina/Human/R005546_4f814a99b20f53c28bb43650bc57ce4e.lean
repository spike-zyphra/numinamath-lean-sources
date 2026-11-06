import Mathlib

/-
Problem Analysis:
We need to count the number of binary sequences of length 10 that contain no two consecutive zeros (00) and no three consecutive ones (111).
-/
theorem combinatorics_608753 
    (a : ℕ → ℝ)
    (b : ℕ → ℝ)
    (c : ℕ → ℝ)
    (a₂ : a 2 = 1)
    (b₂ : b 2 = 1)
    (c₂ : c 2 = 1)
    (h1 : ∀ n : ℕ , a (n + 1) = b n + c n)
    (h2 : ∀ n : ℕ , b (n + 1) = a n)
    (h3 : ∀ n : ℕ , c (n + 1) = b n) : 
    a 10 + b 10 + c 10 = 28 := by

  -- Base cases for n = 2
  have ha3 : a 3 = 2 := by 
    specialize h1 2
    norm_num at h1 
    rw [h1]
    linarith [a₂, b₂, c₂]

  have hb3 : b 3 = 1 := by
    specialize h2 2
    norm_num at h2 
    rw [h2]
    linarith [a₂, b₂, c₂]

  have hc3 : c 3 = 1 := by
    specialize h3 2
    norm_num at h3 
    rw [h3]
    linarith [a₂, b₂, c₂]

  -- Compute values for n = 4
  have ha4 : a 4 = 2 := by 
    specialize h1 3
    norm_num at h1 
    rw [h1]
    linarith [ha3, hb3, hc3]

  have hb4 : b 4 = 2 := by
    specialize h2 3
    norm_num at h2 
    rw [h2]
    linarith [ha3, hb3, hc3]

  have hc4 : c 4 = 1 := by 
    specialize h3 3
    norm_num at h3 
    rw [h3]
    linarith [hb3, ha3, hc3]

  -- Compute values for n = 5
  have ha5 : a 5 = 3 := by 
    specialize h1 4
    norm_num at h1 
    rw [h1]
    linarith [ha4, hb4, hc4]

  have hb5 : b 5 = 2 := by
    specialize h2 4
    norm_num at h2 
    rw [h2]
    linarith [ha4, hb4, hc4]

  have hc5 : c 5 = 2 := by 
    specialize h3 4
    norm_num at h3 
    rw [h3]
    linarith [hb4, ha4, hc4]

  -- Compute values for n = 6
  have ha6 : a 6 = 4 := by 
    specialize h1 5
    norm_num at h1 
    rw [h1]
    linarith [ha5, hb5, hc5]

  have hb6 : b 6 = 3 := by
    specialize h2 5
    norm_num at h2 
    rw [h2]
    linarith [ha5, hb5, hc5]

  have hc6 : c 6 = 2 := by 
    specialize h3 5
    norm_num at h3 
    rw [h3]
    linarith [hb5, ha5, hc5]

  -- Compute values for n = 7
  have ha7 : a 7 = 5 := by 
    specialize h1 6
    norm_num at h1 
    rw [h1]
    linarith [ha6, hb6, hc6]

  have hb7 : b 7 = 4 := by
    specialize h2 6
    norm_num at h2 
    rw [h2]
    linarith [ha6, hb6, hc6]

  have hc7 : c 7 = 3 := by 
    specialize h3 6
    norm_num at h3 
    rw [h3]
    linarith [hb6, ha6, hc6]

  -- Compute values for n = 8
  have ha8 : a 8 = 7 := by 
    specialize h1 7
    norm_num at h1 
    rw [h1]
    linarith [ha7, hb7, hc7]

  have hb8 : b 8 = 5 := by
    specialize h2 7
    norm_num at h2 
    rw [h2]
    linarith [ha7, hb7, hc7]

  have hc8 : c 8 = 4 := by 
    specialize h3 7
    norm_num at h3 
    rw [h3]
    linarith [hb7, ha7, hc7]

  -- Compute values for n = 9
  have ha9 : a 9 = 9 := by 
    specialize h1 8
    norm_num at h1 
    rw [h1]
    linarith [ha8, hb8, hc8]

  have hb9 : b 9 = 7 := by
    specialize h2 8
    norm_num at h2 
    rw [h2]
    linarith [ha8, hb8, hc8]

  have hc9 : c 9 = 5 := by 
    specialize h3 8
    norm_num at h3 
    rw [h3]
    linarith [hb8, ha8, hc8]

  -- Compute values for n = 10 (the final step)
  have ha10 : a 10 = 12 := by 
    specialize h1 9
    norm_num at h1 
    rw [h1]
    linarith [ha9, hb9, hc9]

  have hb10 : b 10 = 9 := by
    specialize h2 9
    norm_num at h2 
    rw [h2]
    linarith [ha9, hb9, hc9]

  have hc10 : c 10 = 7 := by 
    specialize h3 9
    norm_num at h3 
    rw [h3]
    linarith [hb9, ha9, hc9]

  -- Sum the results for n = 10 to get the final answer
  rw [ha10, hb10, hc10]
  all_goals norm_num