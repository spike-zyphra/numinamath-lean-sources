import Mathlib

theorem algebra_12495 {a b : ℝ} (A B : Set ℝ)
    (hA : A = {1, b, a + b}) (hB : B = {a - b, a * b})
    (hAB : A ∩ B = {-1, 0}) :
    a = -1 ∧ b = 0 := by
  have h1 : -1 ∈ A ∩ B := by
    rw [hAB]
    simp
  have h2 : -1 ∈ A := h1.left
  have h3 : -1 ∈ B := h1.right
  have h4 : 0 ∈ A ∩ B := by
    rw [hAB]
    simp
  have h5 : 0 ∈ A := h4.left
  have h6 : 0 ∈ B := h4.right
  rw [hA] at h2 h5
  rw [hB] at h3 h6
  have hA1 : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = b ∨ (-1 : ℝ) = a + b := by 
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at h2 
    simpa using h2 
  have hA5 : (0 : ℝ) = 1 ∨ (0 : ℝ) = b ∨ (0 : ℝ) = a + b := by 
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at h5 
    simpa using h5
  have hB1 : (-1 : ℝ) = a - b ∨ (-1 : ℝ) = a * b := by 
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at h3 
    simpa using h3
  have hB6 : (0 : ℝ) = a - b ∨ (0 : ℝ) = a * b := by 
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at h6 
    simpa using h6
  rcases hA5 with hA5 | hA5 | hA5
  · 
    exfalso
    norm_num at hA5
  · 
    have hb : b = 0 := by
      linarith 
    rw [hb] at hA1 
    rcases hA1 with hA1 | hA1 | hA1
    · 
      exfalso
      norm_num at hA1
    · 
      exfalso
      norm_num at hA1
    · 
      have ha : a = -1 := by 
        nlinarith 
      exact ⟨by linarith, by linarith⟩
  · 
    have hab : a + b = 0 := by
      linarith 
    have ha : a = -b := by 
      linarith 
    rw [ha] at hB6
    rcases hB6 with hB6 | hB6
    · 
      have hb : b = 0 := by 
        nlinarith 
      have ha : a = 0 := by 
        linarith 
      rw [hb, ha] at hA1
      norm_num at hA1
    · 
      have hb : b = 0 := by 
        nlinarith 
      have ha : a = 0 := by 
        linarith 
      rw [hb, ha] at hA1
      norm_num at hA1