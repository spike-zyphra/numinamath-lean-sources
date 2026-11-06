import Mathlib

theorem algebra_21293 : { (a, b) : ℝ × ℝ | {(x, y) | 3 * a * x + 3 * y = 5 * b ∧ 2 * x + y = 5}.Infinite } = {(2, 3)} := by
  ext ⟨a, b⟩
  simp
  constructor
  · -- Assume the solution set is infinite, show $(a, b) = (2, 3)$
    intro h
    by_cases ha : a = 2
    · -- If a = 2, show that b = 3
      have hb : b = 3 := by
        by_contra h1
        push_neg at h1
        have h3 : {(x, y) : ℝ × ℝ | 3 * a * x + 3 * y = 5 * b ∧ 2 * x + y = 5} = ∅ := by
          ext ⟨x, y⟩
          simp
          intro h1 h2
          have h7 : y = 5 - 2 * x := by linarith
          rw [h7] at h1
          have h6 : (3 * a - 6 : ℝ) = 0 := by
            rw [show a = (2 : ℝ) by linarith [ha]]
            norm_num
          have h4 : (3 * a - 6) * x + 15 = 5 * b := by
            nlinarith
          rw [h6] at h4
          have h8 : (15 : ℝ) = 5 * b := by 
            linarith
          have h10 : b = 3 := by
            nlinarith
          tauto
        rw [h3] at h
        simp at h
      tauto
    · -- If a ≠ 2, show contradiction
      have h4 : {(x, y) : ℝ × ℝ | 3 * a * x + 3 * y = 5 * b ∧ 2 * x + y = 5} = {( (5 * b - 15) / (3 * a - 6), 5 - 2 * ((5 * b - 15) / (3 * a - 6)) )} := by
        have ha1 : 3 * a - 6 ≠ 0 := by
          intro h7
          have h8 : a = 2 := by linarith
          tauto
        ext ⟨x, y⟩
        simp
        constructor
        · -- Assume (x,y) is in the solution set.
          rintro ⟨h1, h2⟩
          have h7 : y = 5 - 2 * x := by linarith
          have h8 : (3 * a - 6) * x = 5 * b - 15 := by
            rw [h7] at h1
            linarith
          have hx1 : x = (5 * b - 15) / (3 * a - 6) := by 
            field_simp [ha1]
            linarith
          have hy1 : y = 5 - 2 * ((5 * b - 15) / (3 * a - 6)) := by
            rw [show x = (5 * b - 15) / (3 * a - 6) by linarith [hx1]] at h7
            linarith
          simp [hx1, hy1]
        · -- Assume (x,y) = ( (5 * b - 15) / (3 * a - 6), 5 - 2 * ((5 * b - 15) / (3 * a - 6)) ), show it's in the solution set.
          rintro ⟨rfl, rfl⟩
          constructor
          · -- Check the first equation.
            field_simp [show (3 * a - 6 : ℝ) ≠ 0 by 
              intro h7
              have h8 : a = 2 := by linarith
              tauto
            ]
            all_goals
              linarith
          · -- Check the second equation.
            field_simp [show (3 * a - 6 : ℝ) ≠ 0 by 
              intro h7
              have h8 : a = 2 := by linarith
              tauto
            ]
            all_goals
              linarith
      rw [h4] at h
      simp at h
  · -- Assume (a, b) = (2, 3), show the solution set is infinite
    rintro ⟨rfl, rfl⟩
    apply Set.infinite_of_injective_forall_mem (f := fun (t : ℕ) => ((t : ℝ), 5 - 2 * (t : ℝ)))
    · -- Show f is injective
      intro n m h
      simp [Prod.ext_iff] at h
      all_goals 
        linarith
    · -- Show all points in the image satisfy the system
      intro n
      simp [Prod.ext_iff]
      all_goals
        ring_nf <;> norm_num