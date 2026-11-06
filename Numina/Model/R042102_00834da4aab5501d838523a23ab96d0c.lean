import Mathlib

theorem algebra_199092 {a : ℕ → ℝ} (ha : ∀ n, Odd n → a n = -4)
    (ha' : ∀ n, Even n → a n = 7) :
    ∀ n, a n = 1.5 + (-1) ^ n * 5.5 := by 
  intro n
  by_cases h : Even n
  · -- n is even
    have h1 : a n = 7 := ha' n h
    rw [h1]
    have h3 : (-1 : ℝ) ^ n = 1 := by 
      obtain ⟨k, hk⟩ := h 
      rw [show n = 2 * k by omega]
      have h4 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) = 1 := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_add, pow_mul] at ih ⊢ 
          <;> nlinarith 
      specialize h4 k 
      simpa using h4 
    rw [h3] 
    norm_num 
  · -- n is odd
    have h1 : Odd n := by 
      simp at h ⊢ 
      tauto 
    have h2 : a n = -4 := ha n h1
    rw [h2] 
    have h3 : (-1 : ℝ) ^ n = -1 := by 
      have h1' : ¬Even n := by 
        simp at h ⊢ 
        tauto 
      have h4 : Odd n := by 
        simp at h ⊢ 
        tauto 
      rcases h4 with ⟨k, hk⟩ 
      rw [show n = 2 * k + 1 by omega] 
      have h5 : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) = -1 := by 
        intro k 
        induction k with 
        | zero => 
          norm_num 
        | succ k ih => 
          simp [pow_add, pow_mul] at ih ⊢ 
          <;> nlinarith 
      specialize h5 k 
      simpa using h5 
    rw [h3] 
    norm_num