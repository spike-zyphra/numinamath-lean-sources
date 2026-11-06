import Mathlib

theorem algebra_2400 {f : ℝ → ℝ} (hf0 : f 0 = 1 / 2)
    (hfn : ∀ x y, f (x + y) = f x * f (-y) + f y * f (-x)) :
    ∃ c, ∀ x, f x = c := by
  use 1 / 2
  intro x 
  have h1 : ∀ x : ℝ, f x = f (-x) := by 
    intro x 
    have eq1 := hfn x 0 
    simp [hf0] at eq1 
    have eq2 : f x = f (-x) := by 
      nlinarith 
    exact eq2 
  have eq2 := hfn x (-x) 
  simp [show x + -x = (0 : ℝ) by ring, show -(-x : ℝ) = x by ring, hf0] at eq2 
  have eq3 : f (-x) = f x := by 
    linarith [h1 x] 
  rw [eq3] at eq2 
  have eq4 : (f x) ^ 2 = 1 / 4 := by 
    nlinarith 
  have eq5 : f x = 1 / 2 ∨ f x = -1 / 2 := by 
    have h1 : (f x) ^ 2 - 1 / 4 = 0 := by nlinarith 
    have h2 : (f x - 1 / 2) * (f x + 1 / 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h2) with h3 h4 
    · left 
      linarith 
    · right 
      linarith 
  cases eq5 with 
  | inl h => 
    linarith 
  | inr h => 
    have h6 := hfn (x / 2) (x / 2) 
    have eq4 := h1 (x / 2) 
    have eq5 : f (- (x / 2 : ℝ)) = f (x / 2) := by 
      linarith [eq4] 
    simp [show (x / 2 : ℝ) + (x / 2 : ℝ) = (x : ℝ) by ring, show - (x / 2 : ℝ) = - (x / 2 : ℝ) by ring, eq5] at h6 
    have eq6 : f x = 2 * (f (x / 2)) ^ 2 := by 
      nlinarith 
    rw [h] at eq6 
    nlinarith [sq_nonneg (f (x / 2)), eq6]