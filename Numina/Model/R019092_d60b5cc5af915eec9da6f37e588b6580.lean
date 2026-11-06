import Mathlib

theorem algebra_320662 {f : ℝ → ℝ → ℝ}
    (h1 : ∀ x, f x x = x)
    (h2 : ∀ x y k, f (k * x) (k * y) = k * f x y)
    (h3 : ∀ x1 x2 y1 y2, f (x1 + x2) (y1 + y2) = f x1 y1 + f x2 y2)
    (h4 : ∀ x y, f x y = f y ((x + y) / 2)) :
    f = fun x y => x / 3 + 2 * y / 3 := by

  -- First find f 0 0.
  have h5 : f 0 0 = 0 := by
    have h00 : f (0 + 0) (0 + 0) = f 0 0 + f 0 0 := by
      apply h3 0 0 0 0
    simp at h00 ⊢
    linarith

  -- Find f x 0.
  have h5a : ∀ x, f x 0 = x * (f 1 0) := by
    intro x
    have h13 : f (x * 1) (x * (0 : ℝ)) = x * f 1 (0 : ℝ) := by 
      apply h2 1 (0 : ℝ) x 
    simp at h13 ⊢
    linarith

  -- Find f 0 y.
  have h5b : ∀ y, f 0 y = y * (f 0 1) := by
    intro y
    have h13 : f (y * (0 : ℝ)) (y * (1 : ℝ)) = y * f (0 : ℝ) (1 : ℝ) := by 
      apply h2 0 1 y 
    simp at h13 ⊢
    linarith

  -- Prove that f x y = f x 0 + f 0 y.
  have h5c : ∀ x y, f x y = f x 0 + f 0 y := by
    intro x y
    have h18 : f (x + 0) (0 + y) = f x 0 + f 0 y := by
      apply h3 x 0 0 y
    simp at h18 ⊢
    linarith

  -- Use condition (1): f x x = x.
  have h5d : f 1 0 + f 0 1 = 1 := by
    have h19 : f 1 1 = 1 := h1 1
    have h20 : f 1 1 = f 1 0 + f 0 1 := by
      apply h5c 1 1
    linarith [h19, h20]

  -- Use condition (4) to find relation between f 1 0 and f 0 1.
  have h5f : f 1 0 = 1 / 3 := by
    have eq1 : f 1 0 = f 0 ((1 + (0 : ℝ)) / 2) := by
      apply h4 1 0
    have eq2 : f 0 ((1 + (0 : ℝ)) / 2) = ( (1 + (0 : ℝ)) / 2 ) * (f 0 1) := by
      apply h5b
    have eq3 : f 1 0 = (1 / 2) * (f 0 1) := by 
      rw [eq1, eq2]
      all_goals norm_num 
    have eq4 : f 1 0 + f 0 1 = 1 := h5d
    nlinarith [eq3, eq4]

  -- Solving for f 0 1.
  have h5g : f 0 1 = 2 / 3 := by
    have eq1 : f 1 0 + f 0 1 = 1 := h5d
    have eq3 : f 1 0 = 1 / 3 := h5f
    linarith [eq1, eq3]

  -- Final result.
  funext x y
  have eq2 : f x y = f x 0 + f 0 y := h5c x y
  have eq3 : f x 0 = x * (1 / 3) := by
    have h12 : f x 0 = x * (f 1 0) := h5a x
    rw [h12, h5f]
  have eq4 : f 0 y = y * (2 / 3) := by
    have h13 : f 0 y = y * (f 0 1) := h5b y
    rw [h13, h5g]
  rw [eq3, eq4] at eq2
  linarith [eq2]