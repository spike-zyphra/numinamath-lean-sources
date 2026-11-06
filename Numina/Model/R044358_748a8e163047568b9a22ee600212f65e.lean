import Mathlib

theorem algebra_9763 {a : ℕ → ℝ} (ha2 : a 2 = 1 / 4) (han : ∀ n, a (n + 1) = (2 * a n - 1) / (2 * a n)) : a 2023 = -1 := by 
  have a2 : a 2 = 1 / 4 := ha2
  have a3 : a 3 = -1 := by 
    rw [han 2]
    rw [a2]
    norm_num 
  have a4 : a 4 = 3 / 2 := by 
    rw [han 3]
    rw [a3]
    norm_num 
  have a5 : a 5 = 2 / 3 := by 
    rw [han 4]
    rw [a4]
    norm_num 
  have a6 : a 6 = 1 / 4 := by 
    rw [han 5]
    rw [a5]
    norm_num 
  have h1 : ∀ k : ℕ, a (4 * k + 2) = 1 / 4 ∧ a (4 * k + 3) = -1 ∧ a (4 * k + 4) = 3 / 2 ∧ a (4 * k + 5) = 2 / 3 := by 
    intro k 
    induction k with 
    | zero => 
      constructor 
      · -- a 2 
        norm_num [a2] 
      constructor 
      · -- a 3 
        norm_num [a3] 
      constructor 
      · -- a 4 
        norm_num [a4] 
      · -- a 5 
        norm_num [a5] 
    | succ k ih => 
      have h2 : a (4 * (k + 1) + 2) = 1 / 4 := by 
        have h6 : a (4 * k + 6) = 1 / 4 := by 
          rw [han (4 * k + 5)]
          have h5 : a (4 * k + 5) = 2 / 3 := by 
            tauto 
          rw [h5]
          norm_num 
        have h7 : 4 * (k + 1) + 2 = 4 * k + 6 := by omega 
        rw [h7]
        linarith 
      have h3 : a (4 * (k + 1) + 3) = -1 := by 
        have h7 : a (4 * k + 7) = -1 := by 
          rw [han (4 * k + 6)]
          have h6 : a (4 * k + 6) = 1 / 4 := by 
            tauto 
          rw [h6]
          norm_num 
        have h8 : 4 * (k + 1) + 3 = 4 * k + 7 := by omega 
        rw [h8]
        linarith 
      have h4 : a (4 * (k + 1) + 4) = 3 / 2 := by 
        have h8 : a (4 * k + 8) = 3 / 2 := by 
          rw [han (4 * k + 7)]
          have h7 : a (4 * k + 7) = -1 := by 
            tauto 
          rw [h7]
          norm_num 
        have h9 : 4 * (k + 1) + 4 = 4 * k + 8 := by omega 
        rw [h9]
        linarith 
      have h5 : a (4 * (k + 1) + 5) = 2 / 3 := by 
        have h9 : a (4 * k + 9) = 2 / 3 := by 
          rw [han (4 * k + 8)]
          have h8 : a (4 * k + 8) = 3 / 2 := by 
            tauto 
          rw [h8]
          norm_num 
        have h10 : 4 * (k + 1) + 5 = 4 * k + 9 := by omega 
        rw [h10]
        linarith 
      exact ⟨h2, h3, h4, h5⟩ 
  have h2 : a 2023 = -1 := by 
    specialize h1 505 
    norm_num at h1 ⊢ 
    linarith [h1] 
  exact h2