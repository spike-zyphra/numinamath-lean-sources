import Mathlib

theorem algebra_6302 {f : ℝ → ℝ} (hf : f = fun x => abs (Real.sin (x / 2))^3 + abs (Real.sin (x / 5))^5) :
    ∀ x, f (x + 10 * Real.pi) = f x := by
  intro x 
  rw [hf]
  have h2 : abs (Real.sin ((x + 10 * Real.pi) / 2)) ^ 3 + abs (Real.sin ((x + 10 * Real.pi) / 5)) ^ 5 =
      abs (Real.sin (x / 2)) ^ 3 + abs (Real.sin (x / 5)) ^ 5 := by 
    have h3 : Real.sin ((x + 10 * Real.pi) / 2) = - Real.sin (x / 2) := by 
      have h4 : (x + 10 * Real.pi) / 2 = x / 2 + 5 * Real.pi := by 
        ring 
      rw [h4] 
      have h5 : Real.sin (x / 2 + 5 * Real.pi) = Real.sin (x / 2 + 4 * Real.pi + Real.pi) := by ring_nf
      rw [h5] 
      have h6 : Real.sin (x / 2 + 4 * Real.pi + Real.pi) = Real.sin (x / 2 + Real.pi) := by 
        have h7 : Real.sin (x / 2 + 4 * Real.pi + Real.pi) = Real.sin (x / 2 + Real.pi) := by
          have h8 : x / 2 + 4 * Real.pi + Real.pi = (x / 2 + Real.pi) + 4 * Real.pi := by ring
          rw [h8]
          have h9 : Real.sin ((x / 2 + Real.pi) + 4 * Real.pi) = Real.sin (x / 2 + Real.pi) := by 
            have h10 : Real.sin ((x / 2 + Real.pi) + 4 * Real.pi) = Real.sin ((x / 2 + Real.pi) + 2 * Real.pi + 2 * Real.pi) := by ring_nf
            rw [h10]
            rw [Real.sin_add, Real.sin_add]
            simp [Real.sin_two_pi, Real.cos_two_pi]
            <;> ring
          linarith 
        linarith 
      have h10 : Real.sin (x / 2 + Real.pi) = - Real.sin (x / 2) := by 
        rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
        ring 
      rw [h6, h10] 
    have h4 : Real.sin ((x + 10 * Real.pi) / 5) = Real.sin (x / 5) := by 
      have h5 : (x + 10 * Real.pi) / 5 = x / 5 + 2 * Real.pi := by 
        ring 
      rw [h5] 
      have h6 : Real.sin (x / 5 + 2 * Real.pi) = Real.sin (x / 5) := by 
        have h7 : Real.sin (x / 5 + 2 * Real.pi) = Real.sin (x / 5) := by 
          rw [show x / 5 + 2 * Real.pi = x / 5 + Real.pi + Real.pi by ring]
          rw [Real.sin_add, Real.sin_add]
          simp [Real.sin_pi, Real.cos_pi]
          <;> ring
        linarith 
      linarith 
    have h7 : abs (Real.sin ((x + 10 * Real.pi) / 2)) = abs (Real.sin (x / 2)) := by 
      rw [h3] 
      all_goals 
        simp 
    have h8 : abs (Real.sin ((x + 10 * Real.pi) / 5)) = abs (Real.sin (x / 5)) := by 
      rw [h4] 
    rw [h7, h8] 
  simpa using h2