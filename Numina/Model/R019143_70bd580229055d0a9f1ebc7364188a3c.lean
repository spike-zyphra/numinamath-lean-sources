import Mathlib

theorem algebra_3112 (m : ℚ) (h : ¬∃ f : ℚ → ℚ, ∀ x : ℚ, (x = -2 * m + 1 → f x = -4) ∧ (x = -6 * m + 8 → f x = 0)) :
    m = 7 / 4 := by
  by_contra h1
  push_neg at h1

  have h2 : -2 * m + 1 ≠ -6 * m + 8 := by
    intro h3
    have h3' : 4 * m = 7 := by linarith
    have h4' : m = 7 / 4 := by linarith
    contradiction
  
  have h3 : ∃ f : ℚ → ℚ, ∀ x : ℚ, (x = -2 * m + 1 → f x = -4) ∧ (x = -6 * m + 8 → f x = 0) := by 
    use fun x => 
      if x = -2 * m + 1 then 
        -4 
      else if x = -6 * m + 8 then 
        0 
      else 
        (0 : ℚ)
  
    intro x
    constructor 
    · -- First implication
      intro h_eq
      have h' : (fun x => 
        if x = -2 * m + 1 then 
          -4 
        else if x = -6 * m + 8 then 
          0 
        else 
          (0 : ℚ)
      ) x = -4 := by 
        simp [h_eq] at *
        <;> try { tauto }
        all_goals try { nlinarith }
        all_goals try { linarith }
      assumption
  
    · -- Second implication
      intro h_eq
      have h' : (fun x => 
        if x = -2 * m + 1 then 
          -4 
        else if x = -6 * m + 8 then 
          0 
        else 
          (0 : ℚ)
      ) x = 0 := by 
        simp [h_eq] at *
        all_goals try { 
          have hne : ((-6 * m + 8) : ℚ) ≠ (-2 * m + 1) := by
            intro h'
            have h2' : 4 * m = 7 := by linarith
            have h2m : m = 7 / 4 := by linarith
            contradiction 
          tauto 
          <;> try { nlinarith } 
        }
        all_goals try { 
          nlinarith 
        }
        all_goals try { 
          tauto 
        }
        all_goals try { 
          linarith 
        }
      assumption
  
  exfalso
  exact h h3