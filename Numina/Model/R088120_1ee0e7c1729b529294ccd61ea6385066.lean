import Mathlib

theorem algebra_10302 {f g : ℝ → ℝ} (hf : f = fun x => 3 * x ^ 3 + 2)
    (hg : g.RightInverse f) (x : ℝ) (hx : g x = 4) : x = 194 := by 
  have h1 : g x = 4 := hx
  have h3 : f 4 = (194 : ℝ) := by 
    rw [hf]
    norm_num 
  have h5 : ∀ a b : ℝ, g a = g b → a = b := by 
    intro a b h_eq
    have h_right : f (g a) = a := by 
      apply hg
    have h_right_b : f (g b) = b := by 
      apply hg
    have h_eq' : f (g a) = f (g b) := by 
      rw [h_eq]
    rw [h_right] at h_eq'
    rw [h_right_b] at h_eq'
    linarith 
  have h7 : f (g 194) = 194 := by 
    apply hg
  have h8 : g 194 = 4 := by 
    have h9 : f (g 194) = 194 := by 
      apply hg
    have h10 : f (g 194) = 3 * (g 194) ^ 3 + 2 := by 
      rw [hf]
    rw [h10] at h9 
    nlinarith [sq_nonneg (g 194 - 4), sq_nonneg (g 194 + 4), sq_nonneg (g 194), sq_nonneg (g 194 - 2)]
  -- Now we need to show that x = 194. We know that g(x) = 4 and g(194) = 4.
  have h_eq : g x = g 194 := by 
    rw [h1, h8]
  -- Using injectivity of g
  have h6 : x = (194 : ℝ) := by 
    apply h5 x 194 
    exact h_eq 
  exact h6 
  all_goals linarith 
  all_goals try { norm_num }
  all_goals try { linarith }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    nlinarith 
  }