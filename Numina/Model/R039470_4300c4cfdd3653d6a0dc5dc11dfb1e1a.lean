import Mathlib

theorem algebra_305028 {f : ℝ → ℝ} (h : ∀ x y, f (f x + f y) = f x + y) : f 2011 = 2011 := by

  have injective : ∀ x y, f x = f y → x = y := by
    intro x y h_eq
    have eq1 := h 0 x 
    have eq2 := h 0 y
    have eq3 : f (f 0 + f x) = f (f 0 + f y) := by 
      rw [show f x = f y by linarith [h_eq]]
    have eq4 : f (f 0 + f x) = f 0 + x := by 
      simpa using eq1 
    have eq5 : f (f 0 + f y) = f 0 + y := by 
      simpa using eq2 
    rw [eq4] at eq3 
    rw [eq5] at eq3 
    linarith

  have f0_eq0 : f 0 = 0 := by 
    have eq1 := h 0 0 
    have eq2 : f (2 * f 0) = f 0 := by 
      have eq1' : f (f 0 + f 0) = f 0 + (0 : ℝ) := by 
        simpa using eq1 
      have eq1'' : f (2 * f 0) = f 0 := by 
        ring_nf at eq1' ⊢ 
        all_goals linarith 
      exact_mod_cast eq1'' 
    have eq3 := injective (2 * f 0) (0) (by 
      have eq5 : f (2 * f 0) = f 0 := eq2 
      have eq6 : f (2 * f 0) = f (0 : ℝ) := by 
        rw [eq5] 
        all_goals 
          simp 
      exact_mod_cast eq6 
    )
    norm_num at eq3 ⊢ 
    linarith 
  have h1 : ∀ a b, f a + b = f b + a := by 
    intro a b 
    have eq1 := h a b 
    have eq2 := h b a 
    have eq3 : f (f a + f b) = f (f b + f a) := by 
      rw [show f a + f b = f b + f a by ring]
    have eq4 : f (f a + f b) = f a + b := by 
      simpa using eq1 
    have eq5 : f (f b + f a) = f b + a := by 
      simpa using eq2 
    rw [eq4] at eq3 
    rw [eq5] at eq3 
    all_goals linarith 
  have h2011 : f 2011 = 2011 := by 
    have eq1 := h1 2011 0 
    rw [f0_eq0] at eq1 
    linarith

  exact h2011