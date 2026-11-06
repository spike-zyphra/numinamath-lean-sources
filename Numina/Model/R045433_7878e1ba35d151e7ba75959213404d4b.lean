import Mathlib

theorem algebra_269637 :
    {d : ℝ | 
    ∃ x : ℝ, 
    let time_L : ℝ := (3*x)/(5*4.5) + (2*x)/(5*30) 
    let time_J : ℝ := (3*x/5)/5 + (9*x/10)/30 
    time_J = time_L + 1/15 ∧ 
    d = x + 3*x/2 
    } = {50} := by 
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- Assume h : (∃ x, time_J = time_L + 1/15 ∧ d = x + 3*x/2)
    rintro ⟨x, ⟨h_eq, h_eq2⟩⟩ 
    have time_L_eq : (3*x)/(5*4.5) + (2*x)/(5*30) = (3*x)/(5*4.5) + (2*x)/(5*30) := by rfl
    have time_J_eq : (3*x/5)/5 + (9*x/10)/30 = (3*x/5)/5 + (9*x/10)/30 := by rfl
    have eq1 : (3*x/5)/5 + (9*x/10)/30 = (3*x/(5*4.5) + (2*x)/(5*30)) + 1/15 := by 
      have h_eq3 : (3*x/5)/5 + (9*x/10)/30 = (3*x/(5*4.5) + (2*x)/(5*30)) + 1/15 := by
        simpa [time_L_eq, time_J_eq] using h_eq 
      linarith
    have eq7 : x = 20 := by 
      ring_nf at eq1 ⊢ 
      field_simp at eq1 ⊢ 
      nlinarith 
    have h1 : d = 50 := by
      rw [show x = 20 by linarith [eq7] ] at h_eq2
      linarith 
    linarith
  · -- Assume h : d = 50
    intro h 
    rw [h] 
    use 20 
    constructor
    · -- Show that time_J = time_L + 1/15 for x = 20
      norm_num 
    · -- Show that 50 = 20 + 3*20/2
      norm_num