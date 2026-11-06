import Mathlib

theorem algebra_115 {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (W1 W2 : Submodule F V) (hW1 : W1 ≠ ⊤) (hW2 : W2 ≠ ⊤) :
    ∃ x : V, x ∉ ↑W1 ∧ x ∉ ↑W2 := by

  have hb1 : ∃ b1 : V, b1 ∉ W1 := by
    by_contra h
    push_neg at h
    have h1_eq : W1 = ⊤ := by
      ext v
      simpa using h v
    contradiction
  
  have hb2 : ∃ b2 : V, b2 ∉ W2 := by
    by_contra h
    push_neg at h
    have h2_eq : W2 = ⊤ := by
      ext v
      simpa using h v
    contradiction
  
  rcases hb1 with ⟨b1, hb1⟩
  rcases hb2 with ⟨b2, hb2⟩
  by_cases h1 : b1 ∉ W2
  · -- If b1 is not in W2, then we can take x = b1
    refine ⟨b1, hb1, h1⟩
  · -- b1 ∈ W2
    have h1' : b1 ∈ W2 := by 
      simpa using h1
  
    by_cases h2 : b2 ∉ W1
    · -- If b2 is not in W1 then we can take x = b2
      refine ⟨b2, h2, hb2⟩
    · -- b2 ∈ W1
      have h2' : b2 ∈ W1 := by
        simpa using h2
  
      refine ⟨b1 + b2, ?_, ?_⟩
  
      · -- Show b1 + b2 ∉ W1
        intro h
        have h3 : b1 ∈ W1 := by
          have hw1 : (b1 + b2) ∈ W1 := h
          have hw2 : b2 ∈ W1 := h2'
          have h4 : b1 = (b1 + b2) - b2 := by
            simp [add_right_inj, add_left_inj]
          rw [h4]
          apply W1.sub_mem hw1 hw2
  
        contradiction
  
      · -- Show b1 + b2 ∉ W2
        intro h
        have h4 : b2 ∈ W2 := by
          have hw1 : (b1 + b2) ∈ W2 := h
          have hw2 : b1 ∈ W2 := h1'
          have h4 : b2 = (b1 + b2) - b1 := by
            simp [add_right_inj, add_left_inj]
          rw [h4]
          apply W2.sub_mem hw1 hw2
  
        contradiction