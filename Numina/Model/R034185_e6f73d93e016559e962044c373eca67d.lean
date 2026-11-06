import Mathlib

theorem algebra_19720{s: Set (ℝ × ℝ)} (a b : ℝ)
  (hs: s = {(x,y):ℝ × ℝ | 2*a*x+2*y=b ∧ 5*x+y=-3}):
  Set.Infinite s ↔ a = 5 ∧ b = -6 := by
  constructor
  · -- Assume s is infinite, prove a = 5 ∧ b = -6
    intro h
    by_cases ha : a = 5
    · -- If a = 5, check b
      have ha' : a = 5 := ha
      have hb : b = -6 := by
        by_contra hne
        push_neg at hne
        have h1 : s = ∅ := by
          rw [hs]
          ext ⟨x, y⟩
          simp
          intro h1 h2
          have eq1 : 10 * x + 2 * y = b := by 
            rw [show a = 5 by linarith] at h1
            nlinarith
          have eq2 : 5 * x + y = -3 := by linarith
          have eq3 : b = -6 := by
            have h10 : y = -3 - 5 * x := by linarith [eq2]
            rw [h10] at eq1
            nlinarith
          exfalso
          tauto
        rw [h1] at h
        simp at h
      constructor
      · exact ha
      · exact hb
    · -- If a ≠ 5, prove contradiction
      have ha' : a ≠ 5 := ha
      have h2 : ¬ Set.Infinite s := by
        have h3 : {(x, y) : ℝ × ℝ | 2 * a * x + 2 * y = b ∧ 5 * x + y = -3} = {( (b + 6) / (2 * a - 10), -3 - 5 * ((b + 6) / (2 * a - 10)) )} := by
          ext ⟨x, y⟩
          simp 
          constructor
          · -- Assume h1 ∧ h2 
            rintro ⟨h1, h2⟩
            have eq1 : 5 * x + y = -3 := by linarith 
            have h3 : y = -3 - 5 * x := by linarith
            rw [h3] at h1
            have eq2 : (2 * a - 10) * x = b + 6 := by 
              nlinarith
            have h4 : (2 * a - 10) ≠ 0 := by 
              by_contra h'
              have : a = 5 := by 
                nlinarith 
              tauto
            have hx : x = (b + 6) / (2 * a - 10) := by 
              field_simp 
              linarith
            have hy : y = -3 - 5 * ((b + 6) / (2 * a - 10)) := by
              have h4 : y = -3 - 5 * x := by linarith 
              rw [h4]
              rw [hx]
            simp [hx, hy]
          · -- Show the point satisfies both equations
            rintro ⟨rfl, rfl⟩
            constructor
            · -- Check 2*a*x + 2*y = b
              field_simp [(show (2 * a - 10) ≠ 0 by
                by_contra h'
                have : a = 5 := by 
                  nlinarith
                tauto 
              )]
              <;> nlinarith 
            · -- Check 5*x + y = -3
              field_simp 
              <;> nlinarith
        rw [hs] at *
        rw [h3]
        simp 
      exfalso 
      tauto 
  · -- Assume a = 5 ∧ b = -6, prove s is infinite
    rintro ⟨rfl, rfl⟩
    rw [hs]
    apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => ( (t : ℝ), -3 - 5 * (t : ℝ) ) )
    · -- Show f is injective
      intro n m h
      simp [Prod.ext_iff] at h 
      omega
    · -- Show all elements of f are in s 
      intro n
      simp [Prod.ext_iff]
      all_goals
        ring_nf