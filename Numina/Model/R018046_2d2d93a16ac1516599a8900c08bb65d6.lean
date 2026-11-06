import Mathlib

theorem algebra_44329 {f : ℝ → ℝ → ℝ} (h : ∀ a b c, f (f a b) c = a + b + c) :
    ∀ a b, f a b = a + b := by 
  have h1 : ∀ c, f (f 0 0) c = c := by 
    intro c 
    specialize h 0 0 c 
    norm_num at h ⊢ 
    linarith 
  have h2 : f 0 0 = (0 : ℝ) := by 
    have h3 : f (f (f 0 0) (f 0 0)) (f 0 0) = f 0 0 + f 0 0 + f 0 0 := by 
      apply h 
    have h4 : f (f (f 0 0) (f 0 0)) (f 0 0) = f 0 0 := by 
      have eq1 : f (f 0 0) (f 0 0) = f 0 0 := by 
        specialize h1 (f 0 0)
        simpa using h1 
      rw [eq1] 
      all_goals 
        have eq4 : f (f 0 0) (f 0 0) = f 0 0 := eq1 
        simpa using eq4 
    -- From h3 and h4 
    linarith 
  have h3 : ∀ c, f 0 c = c := by 
    intro c 
    have eq1 : f (f 0 0) c = c := h1 c 
    rw [show f 0 0 = (0 : ℝ) by linarith [h2] ] at eq1 
    simpa using eq1 
  intro a b 
  have eq1 : f (f 0 a) b = (0 : ℝ) + a + b := h 0 a b 
  have eq2 : f 0 a = a := h3 a 
  rw [eq2] at eq1 
  linarith