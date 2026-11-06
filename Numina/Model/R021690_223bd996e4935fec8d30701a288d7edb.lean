import Mathlib

theorem algebra_127448 {f : ℝ → ℝ} (h : ∀ x y, f (x + abs y) = f (abs x) + f y) :
    ∀ x, f x = 0 := by
  have h1 : f 0 = 0 := by
    have h00 := h 0 0
    norm_num at h00
    linarith

  have h2 : ∀ x, f x = f (abs x) := by
    intro x
    have hx0 := h x 0
    simp [h1] at hx0
    linarith

  have h3 : ∀ y, f (abs y) = 0 := by 
    intro y 
    have h4 := h (-abs y) y
    have eq1 : -abs y + abs y = (0 : ℝ) := by 
      linarith [abs_nonneg y]
    have eq2 : abs (-abs y) = abs (abs y) := by 
      simp [abs_neg]
    have eq3 : abs (abs y) = abs y := by 
      simp [abs_of_nonneg (abs_nonneg y)]
    rw [eq1] at h4 
    rw [eq2, eq3] at h4 
    have h5 : f y = f (abs y) := by 
      apply h2 
    linarith [h1, h5]

  intro x 
  have hx1 : f x = f (abs x) := by 
    apply h2 
  have hx2 : f (abs x) = 0 := by 
    apply h3 
  rw [hx1, hx2]