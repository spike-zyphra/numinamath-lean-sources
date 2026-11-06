import Mathlib

/-- IsLinear denote that a function is linear. -/  
def IsLinear (f : ℝ → ℝ) := ∃ a b, ∀ x, f x = a * x + b 

theorem algebra_4082 {f g : ℝ → ℝ}
    (hf : IsLinear f) (hg : g.RightInverse f)
    (h₁ : ∀ x, f x = 4 * g x + 6) (h₂ : f 1 = 4) : f 2 = 6 := by
  rcases hf with ⟨a, b, hlin⟩
  have eq1 : a + b = (4 : ℝ) := by
    have h11 : f 1 = a * (1 : ℝ) + b := by
      apply hlin
    linarith [h11, h₂]
  have eq3 := h₁ 1
  -- For x = 1, we have f 1 = 4 * g 1 + 6. Since f 1 = 4
  have eq5 : 4 * g 1 = (-2 : ℝ) := by
    have h33 : f 1 = 4 * g 1 + 6 := by
      simpa using eq3
    linarith [h33, h₂]
  -- Now to compute g 1
  have eq8 : g 1 = (-1 / 2 : ℝ) := by
    linarith [eq5]
  have eq9 : f (g 1) = (1 : ℝ) := by 
    apply hg 
  have eq10 : f (g 1) = a * (g 1) + b := by
    apply hlin
  rw [eq10] at eq9 
  rw [eq8] at eq9
  have eq11 : -a / 2 + b = (1 : ℝ) := by
    linarith 
  -- Now we have two equations:
  -- 1. a + b = 4 
  -- 2. -a/2 + b = 1
  -- Subtract the second from the first: (a + b) - (-a/2 + b) = 4 - 1
  -- a + a/2 = 3 => 3a/2 = 3 => a = 2
  have ha : a = (2 : ℝ) := by
    nlinarith [eq1, eq11]
  -- Substitute a = 2 into eq1
  have hb : b = (2 : ℝ) := by 
    linarith [eq1, ha]
  -- Calculate f 2
  have hf2 : f 2 = a * (2 : ℝ) + b := by 
    apply hlin
  rw [hf2] 
  rw [ha, hb] 
  norm_num