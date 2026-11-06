import Mathlib

theorem algebra_107995 {f g : ℝ → ℝ} (hf0 : f 0 = 0)
    (hfg : ∀ x y, g (x - y) ≥ f x * f y + g x * g y) :
    ∀ x, f x ^ 2008 + g x ^ 2008 ≤ 1 := by

  have h1 : g 0 ≥ 0 := by 
    have h1 := hfg 0 0 
    simp [hf0] at h1 
    nlinarith

  have h2 : g 0 ≤ 1 := by
    have h2 := hfg 0 0 
    simp [hf0] at h2
    nlinarith [sq_nonneg (g 0 - 1)]

  intro x
  
  have h3 : g 0 ≥ f x ^ 2 + g x ^ 2 := by 
    specialize hfg x x 
    have h4 : g (x - x) = g 0 := by
      simp 
    rw [h4] at hfg 
    nlinarith

  have h4 : f x ^ 2 + g x ^ 2 ≤ 1 := by 
    nlinarith [h3, h2]

  have h5 : f x ^ 2 ≥ 0 := by 
    apply sq_nonneg 

  have h6 : g x ^ 2 ≥ 0 := by 
    apply sq_nonneg 

  have h7 : f x ^ 2 ≤ 1 := by 
    nlinarith

  have h8 : g x ^ 2 ≤ 1 := by 
    nlinarith

  have h9 : (f x ^ 2) ^ 1004 ≤ f x ^ 2 := by 
    have h10 : f x ^ 2 ≥ 0 := h5 
    have h11 : f x ^ 2 ≤ 1 := h7 
    have h12 : ∀ (n : ℕ), (f x ^ 2) ^ (n + 1) ≤ f x ^ 2 := by
      intro n 
      induction n with 
      | zero => 
        norm_num 
      | succ n ih => 
        have h13 : (f x ^ 2) ^ (n + 1 + 1) = (f x ^ 2) * ((f x ^ 2) ^ (n + 1)) := by 
          ring
        rw [h13] 
        nlinarith [ih, sq_nonneg (f x ^ 2 - 1), h10, h11]

    specialize h12 1003 
    norm_num at h12 ⊢ 
    all_goals nlinarith

  have h10 : (g x ^ 2) ^ 1004 ≤ g x ^ 2 := by
    have h11 : g x ^ 2 ≥ 0 := h6 
    have h12 : g x ^ 2 ≤ 1 := h8 
    have h13 : ∀ (n : ℕ), (g x ^ 2) ^ (n + 1) ≤ g x ^ 2 := by
      intro n 
      induction n with 
      | zero => 
        norm_num 
      | succ n ih => 
        have h14 : (g x ^ 2) ^ (n + 1 + 1) = (g x ^ 2) * ((g x ^ 2) ^ (n + 1)) := by 
          ring 
        rw [h14] 
        nlinarith [ih, sq_nonneg (g x ^ 2 - 1), h11, h12]

    specialize h13 1003 
    norm_num at h13 ⊢ 
    all_goals nlinarith

  have h11 : f x ^ 2008 = (f x ^ 2) ^ 1004 := by 
    ring 
  have h12 : g x ^ 2008 = (g x ^ 2) ^ 1004 := by 
    ring 
  rw [h11] 
  rw [h12] 
  nlinarith [h9, h10, sq_nonneg (f x ^ 2 - g x ^ 2), sq_nonneg (f x), sq_nonneg (g x)]