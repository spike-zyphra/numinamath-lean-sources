import Mathlib

theorem algebra_216077 {f : ℝ → ℝ} (h : ∀ x, f x - (x - 0.5) * f (-x - 1) = 1) :
    ∀ x, x ≠ -0.5 → f x = 1 / (0.5 + x) ∧ f (-0.5) = 0.5 := by
  intro x hx
  have eq1 := h x
  have eq3 := h (-x - 1)
  -- First step is here to look at functional equation for x and for -x -1
  -- h for x gives eq1: f(x) - (x -0.5)*f(-x -1) = 1
  -- h for (-x -1) gives eq3: f(-x -1) - ((-x -1) -0.5)*f(-(-x -1) -1) =1
  -- From eq3, we compute inner expression:
  -- f(-(-x -1) -1) = f(-(-x -1) -1) = f(x +1 -1) = f(x)
  have eq4 : f x = 1 / (0.5 + x) := by
    have eq5 : f x - (x - 0.5) * f (-x - 1) = 1 := by
      simpa using eq1
    have eq6 : f (-x - 1) - ((-x - 1) - 0.5) * f (-(-x - 1) - 1) = 1 := by
      simpa using eq3
    -- Compute values:
    have h1 : (-x - 1 : ℝ) - 0.5 = -x - 1.5 := by ring
    have h2 : -(-x - 1 : ℝ) - 1 = x := by ring
    rw [h1, h2] at eq6
    -- eq6: f(-x -1) - (-x -1.5) * f(x) =1
    have eq7 : f (-x - 1) = 1 + (-x - 1.5) * f x := by linarith
    -- Substitute eq7 into eq5 (original for x):
    rw [eq7] at eq5
    -- This yields f(x) - (x -0.5) * (1 + (-x -1.5) f(x)) =1
    -- Simplify:
    -- f(x) =1 + (x -0.5) * (1 + (-x -1.5) f(x))
    have eq8 : (0.5 + x) ≠ 0 := by
      intro h2 
      apply hx
      have : x = -0.5 := by
        have h3 : (0.5 + x) = 0 := by
          linarith 
        have h4 : x = -0.5 := by
          linarith 
        linarith 
      linarith 
    -- Simplify final term
    field_simp at eq5 ⊢
    ring_nf at eq5 ⊢
    nlinarith [sq_pos_of_ne_zero (show (0.5 + x) ≠ 0 by assumption)]
  -- From functional analysis, assumed form, then gives value at -0.5 as below
  have eq5 : f (-0.5) = 0.5 := by 
    have eq8 := h (-0.5)
    norm_num at eq8 ⊢
    linarith 
  constructor
  · exact eq4 
  · exact eq5