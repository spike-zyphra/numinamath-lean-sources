import Mathlib

theorem number_theory_253246 (x : ℕ → ℕ) (h1 : x 1 = 2) (h2 : x 2 = 7)
    (h : ∀ n ≥ 1, x (n + 2) = (x n * x (n + 1)) % 10) :
    x 1998 = 6 := by 

    have x3 : x 3 = 4 := by simp [h,h1,h2]
    have x4 : x 4 = 8 := by simp [h,h1,h2]
    have x5 : x 5 = 2 := by simp [h,h1,h2]
    have x6 : x 6 = 6 := by simp [h,h1,h2]
    have x7 : x 7 = 2 := by simp [h,h1,h2]
    have x8 : x 8 = 2 := by simp [h,h1,h2]

    --We prove by induction that the sequence has a period of 6.
    have cla : ∀ n:ℕ, x (6*n+3) = 4 ∧ x (6*n+4) = 8 ∧ x (6*n+5) = 2 ∧ x (6*n+6) = 6 ∧ x (6*n+7) = 2 ∧ x (6*n+8) = 2 := by
      intro n
      induction' n with n hn
      
      simp; tauto

      obtain ⟨h3,h4,h5,h6,h7,h8⟩ := hn
      have h9: x (6 * (n + 1) + 3) = 4 := by 
        have : 6 * (n + 1) + 3 = 6 * n + 7 + 2 := by ring
        rw [this]
        rw [h]
        rw [h7,h8]
        linarith
      have h10: x (6 * (n + 1) + 4) = 8 := by 
        have : 6 * (n + 1) + 4 = 6 * n + 8 + 2 := by ring
        rw [this]
        rw [h]
        have : 6 * n + 8 + 1 = 6*(n+1)+3 := by ring
        rw [this]
        rw [h8,h9]
        linarith
      have h11: x (6 * (n + 1) + 5) = 2 := by 
        have : 6 * (n + 1) + 5 = (6*(n+1)+3) +2 := by ring
        rw [this]
        rw [h]
        have : 6 * (n + 1) + 3 + 1 = 6 * (n + 1) + 4 := by ring
        rw [this]
        rw [h9,h10]
        linarith
      have h12: x (6 * (n + 1) + 6) = 6 := by 
        have : 6 * (n + 1) + 6 = (6*(n+1)+4)+2 := by ring
        rw [this]
        rw [h]
        have : 6 * (n + 1) + 4 + 1 = 6 * (n + 1) + 5 := by ring
        rw [this]
        rw [h10,h11]
        linarith
      have h13: x (6 * (n + 1) + 7) = 2 := by 
        have : 6 * (n + 1) + 7 = (6*(n+1)+5) +2 := by ring
        rw [this]
        rw [h]
        have : 6 * (n + 1) + 5 + 1 = 6 * (n + 1) + 6 := by ring
        rw [this]
        rw [h11,h12]
        linarith
      have h14: x (6 * (n + 1) + 8) = 2 := by 
        have : 6 * (n + 1) + 8 = (6*(n+1)+6) +2 := by ring
        rw [this]
        rw [h]
        have : 6 * (n + 1) + 6 + 1 = 6 * (n + 1) + 7 := by ring
        rw [this]
        rw [h12,h13]
        linarith
      tauto
    
    --Simply apply our previous result on the period.
    have : ∀ n ≥ 1, x (6*n+6) = 6 := by
      intro n
      specialize cla n
      tauto
    specialize this 332
    simp at this
    exact this
