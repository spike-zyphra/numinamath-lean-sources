import Mathlib

theorem number_theory_229610 (a : ℕ → ℤ) (ha1 : 0 < a 1)
    (han : ∀ n, a (n + 1) = if Even (a n) then a n / 2 else 3 * a n + 1)
    (hsum : a 1 + a 2 + a 3 = 29) : a 1 = 5 := by
  have ha2 : a 2 = if Even (a 1) then a 1 / 2 else 3 * a 1 + 1 := by 
    specialize han 1 
    simpa using han 
  have ha3 : a 3 = if Even (a 2) then a 2 / 2 else 3 * a 2 + 1 := by 
    specialize han 2 
    simpa using han 
  by_cases h1 : Even (a 1)
  · -- Assume a 1 is even
    have ha2' : a 2 = a 1 / 2 := by 
      rw [ha2]
      simp [h1]
    by_cases h2 : Even (a 2)
    · -- Assume a 2 is even 
      have ha3' : a 3 = a 2 / 2 := by 
        rw [ha3]
        simp [h2]
      rw [ha2', ha3'] at hsum 
      exfalso
      have : a 1 % 2 = 0 := by 
        obtain ⟨k, hk⟩ := h1 
        omega 
      omega 
    · -- Assume a 2 is odd 
      have ha3' : a 3 = 3 * a 2 + 1 := by 
        rw [ha3]
        simp [show ¬Even (a 2) by tauto]
      rw [ha2', ha3'] at hsum 
      exfalso 
      have : a 1 % 2 = 0 := by 
        obtain ⟨k, hk⟩ := h1 
        omega 
      omega 
  · -- Assume a 1 is odd 
    have h1 : ¬Even (a 1) := by 
      simpa using h1 
    have ha2' : a 2 = 3 * a 1 + 1 := by 
      rw [ha2]
      simp [h1]
    have h2 : Even (a 2) := by 
      rw [ha2']
      have h_1 : a 1 % 2 = 1 := by 
        have h1' : ¬Even (a 1) := by 
          simpa using h1 
        have : a 1 % 2 = 1 := by 
          by_contra h 
          push_neg at h 
          have : Even (a 1) := by 
            refine' ⟨(a 1) / 2, by omega⟩ 
          contradiction 
        omega 
      have : (3 * a 1 + 1) % 2 = 0 := by 
        omega 
      have : Even (3 * a 1 + 1) := by 
        refine ⟨(3 * a 1 + 1) / 2, by omega⟩ 
      exact_mod_cast this 
    have ha3' : a 3 = a 2 / 2 := by 
      rw [ha3]
      simp [h2]
    rw [ha2', ha3'] at hsum 
    have h2 : a 1 = 5 := by 
      have : a 1 % 2 = 1 := by 
        have h1' : ¬Even (a 1) := by 
          simpa using h1 
        have : a 1 % 2 = 1 := by 
          by_contra h 
          push_neg at h 
          have : Even (a 1) := by 
            refine' ⟨(a 1) / 2, by omega⟩ 
          contradiction 
        omega 
      omega 
    linarith