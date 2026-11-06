import Mathlib

theorem algebra_268276 {f g : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x)
    (hg : ∀ x, g (-x) = -g x)
    (hfg : ∀ x, g x = f (x - 1))
    (h1 : g 1 = 2003) :
    f 2004 = 2003 := by

  have h2 : f 0 = 2003 := by
    have eq1 : g 1 = f (1 - 1) := hfg 1
    have eq2 : (1 - 1 : ℝ) = 0 := by norm_num
    rw [eq2] at eq1
    linarith [h1, eq1]
  
  have eq6 : ∀ x, f (x + 2) = - f x := by 
    intro x 
    have eq7 : g (-(x + 1)) = -g (x + 1) := by 
      apply hg 
    have eq8 : g (x + 1) = f (x) := by 
      rw [hfg (x + 1)]
      ring_nf 
    have eq9 : g (-(x + 1)) = f (-(x + 2)) := by 
      rw [hfg (-(x + 1))]
      ring_nf
    have eq10 : f (-(x + 2)) = - f (x) := by
      rw [eq8] at eq7 
      rw [eq9] at eq7 
      linarith 
    have eq11 : f (-(x + 2)) = f (x + 2) := by 
      rw [show -(x + 2) = - (x + 2) by ring]
      apply hf 
    rw [eq11] at eq10 
    linarith

  have eq7 : ∀ x, f (x + 4) = f x := by
    intro x 
    have eq8 : f (x + 2) = - f x := eq6 x 
    have eq9 : f (x + 4) = - f (x + 2) := by 
      specialize eq6 (x + 2)
      have eq10 : (x + 2) + 2 = x + 4 := by ring
      rw [eq10] at eq6 
      linarith 
    rw [eq9, eq8] 
    all_goals linarith

  have eq9 : ∀ (n : ℕ), f ((↑n * (4 : ℝ))) = f 0 := by 
    intro n 
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      have eq9 : (↑(n + 1 : ℕ) * (4 : ℝ)) = (↑n * (4 : ℝ)) + 4 := by 
        simp at *
        <;> ring 
      rw [eq9]
      have eq10 : f ((↑n * (4 : ℝ)) + 4) = f (↑n * (4 : ℝ)) := by 
        have eq11 : f ((↑n * (4 : ℝ)) + 4) = f (↑n * (4 : ℝ)) := by 
          specialize eq7 (↑n * (4 : ℝ))
          ring_nf at eq7 ⊢ 
          linarith 
        linarith 
      rw [eq10, ih]

  have eq10 : (2004 : ℝ) = (↑(501 : ℕ) * (4 : ℝ)) := by
    norm_num

  rw [eq10]
  rw [eq9 501]
  linarith [h2]