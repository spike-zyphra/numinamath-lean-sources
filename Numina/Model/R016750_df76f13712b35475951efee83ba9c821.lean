import Mathlib

theorem algebra_189587 (a : ℝ) (A B : Set ℝ)
    (hA : A = {a ^ 2, a + 1, -3}) (hB : B = {a - 3, 2 * a - 1, a ^ 2 + 1})
    (hAB : A ∩ B = {-3}) :
    a = -1 := by

  have h1 : -3 ∈ A ∩ B := by 
    rw [hAB]
    simp 

  have h4 : -3 ∈ B := by 
    have h1' : -3 ∈ A ∩ B := h1 
    exact h1'.2

  rw [hB] at h4 
  simp at h4

  rcases h4 with (h | h | h)
  · -- Case 1: a - 3 = -3, so a = 0
    have ha0 : a = (0 : ℝ) := by linarith 
    -- This leads to a contradiction because if a = 0, then 1 ∈ A ∩ B
    have h5 : (1 : ℝ) ∈ A ∩ B := by 
      have h1_A : (1 : ℝ) ∈ A := by 
        rw [hA]
        simp [ha0]
        all_goals norm_num 
      have h1_B : (1 : ℝ) ∈ B := by 
        rw [hB]
        simp [ha0]
        all_goals norm_num 
      exact ⟨h1_A, h1_B⟩
    
    have h6 : (1 : ℝ) ∈ (A ∩ B) := h5 
    rw [hAB] at h6 
    simp at h6 
    all_goals nlinarith 
  · -- Case 2: 2 * a - 1 = -3, so a = -1 
    have ha : a = (-1 : ℝ) := by linarith 
    linarith 
  · -- Case 3: a ^ 2 + 1 = -3 
    nlinarith [sq_nonneg a]