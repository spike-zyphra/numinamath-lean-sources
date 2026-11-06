import Mathlib

theorem number_theory_172109 (a b c : ℕ) (ha : 0 < a) (hb : a ≤ b) (hc : b ≤ c)
    (h : a * b * c = 2 * (a + b + c)) :
    (a = 2 ∧ b = 2 ∧ c = 4) ∨ (a = 1 ∧ b = 3 ∧ c = 8) ∨ (a = 1 ∧ b = 4 ∧ c = 5) := by

  have h1 : a ≤ 2 := by
    nlinarith [h, ha, hb, hc, mul_pos ha (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
  have h2 : a = 1 ∨ a = 2 := by
    omega

  cases h2 with
  | inl ha1 =>
    -- Now we have a = 1
    have h3 : b ≤ 8 := by
      rw [ha1] at h
      nlinarith [show 0 < b by linarith, show 0 < c by linarith, mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    
    have h4 : b = 3 ∨ b = 4 := by
      rw [ha1] at h
      have h5 : b ≤ 8 := by
        nlinarith
      interval_cases b <;> omega

    cases h4 with
    | inl hb3 =>
      -- Now we have b = 3
      have hc8 : c = 8 := by
        rw [ha1, hb3] at h
        nlinarith

      simp [ha1, hb3, hc8]
    | inr hb4 =>
      -- Now we have b = 4
      have hc5 : c = 5 := by
        rw [ha1, hb4] at h
        nlinarith

      simp [ha1, hb4, hc5]

  | inr ha2 =>
    -- Now we have a = 2
    have h5 : b ≤ 2 := by
      rw [ha2] at h
      nlinarith [show 0 < b by linarith, show 0 < c by linarith, mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    
    have hb2 : b = 2 := by
      nlinarith

    have hc4 : c = 4 := by
      rw [ha2, hb2] at h
      nlinarith

    simp [ha2, hb2, hc4]