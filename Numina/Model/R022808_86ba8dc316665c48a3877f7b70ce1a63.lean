import Mathlib

theorem algebra_308989 {f : ℝ → ℝ} (hodd : ∀ x, f x = -f (-x)) (hf : ∀ x, f (1 - x) = f x) :
    f 2010 = 0 := by

  have h1 : ∀ x, f x = f (x + 2) := by
    intro x
    have eq1 : f (x + 1) = -f x := by
      have eq2 := hf (x + 1)
      have eq3 : 1 - (x + 1 : ℝ) = -x := by ring
      have eq4 : f (1 - (x + 1 : ℝ)) = f (-x) := by rw [eq3]
      simp only [eq4] at eq2
      have eq5 : f x = -f (-x) := hodd x
      linarith
    have eq3 : f (x + 2) = -f (x + 1) := by
      have eq4 := hf (x + 2)
      have eq5 : (1 - (x + 2 : ℝ) ) = - (x + 1 : ℝ) := by ring
      have eq6 : f (1 - (x + 2 : ℝ)) = f (- (x + 1 : ℝ)) := by rw [eq5]
      simp only [eq6] at eq4 
      have eq7 : f (x + 1) = -f (- (x + 1 : ℝ)) := by linarith [hodd (x + 1)]
      linarith
    have l1 : f (x + 2) = f x := by
      linarith [eq1, eq3]
    linarith [l1]
  have h2 : f 2010 = f (0 : ℝ) := by 
    have eq1 : ∀ (k : ℕ), f (0 : ℝ) = f (0 + ((k : ℝ) * 2 : ℝ)) := by 
      intro k 
      induction k with 
      | zero =>
        simp 
      | succ k ih =>
        have eq11 : f (0 + ((k + 1 : ℕ) : ℝ) * 2 ) = f ( (0 + ((k : ℕ) : ℝ) * 2 ) + 2 ) := by
          simp at *
          <;> ring_nf 
        have eq12 : f ( (0 + ((k : ℕ) : ℝ) * 2 ) + 2 ) = f (0 + ((k : ℕ) : ℝ) * 2 ) := by 
          have eq14 : f ( (0 + ((k : ℝ) * 2 : ℝ) ) + 2 ) = f (0 + ((k : ℝ) * 2 : ℝ) ) := by 
            have eq13 : f (0 + ((k : ℝ) * 2 : ℝ) ) = f ( (0 + ((k : ℝ) * 2 : ℝ) ) + 2 ) := by 
              apply h1 
            linarith 
          simpa using eq14 
        have eq13 : f (0 + ((k + 1 : ℕ) : ℝ) * 2 ) = f (0 + ((k : ℕ) : ℝ) * 2 ) := by 
          linarith [eq11, eq12]
        linarith [ih, eq13]
    specialize eq1 1005
    have eq2 : (0 + ((1005 : ℕ) : ℝ) * 2 : ℝ) = (2010 : ℝ) := by 
      norm_num
    rw [eq2] at eq1 
    linarith [eq1]
  have h3 : f (0 : ℝ) = 0 := by 
    have eq1 : f 0 = -f (- (0 : ℝ)) := hodd 0 
    have eq2 : - (0 : ℝ) = (0 : ℝ) := by ring 
    rw [eq2] at eq1 
    linarith 
  rw [h2, h3]