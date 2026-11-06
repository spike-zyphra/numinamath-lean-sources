import Mathlib

theorem algebra_124407 {f : ℝ → ℝ} (h : ∀ x y, f x + f y = 2 * f ((x + y) / 2) * f ((x - y) / 2)) :
    Even f := by
  have h0 : ∀ x, f x + f 0 = 2 * f (x / 2) ^ 2 := by
    intro x
    have h_eq := h x 0
    ring_nf at h_eq ⊢
    linarith

  have h1 : ∀ x, f x = f x * f 0 := by
    intro x
    have eq1 := h x x
    have eq2 : (x + x) / 2 = x := by ring
    have eq3 : (x - x) / 2 = (0 : ℝ) := by ring
    rw [eq2, eq3] at eq1
    have eq3 : f x + f x = 2 * f x * f 0 := by
      linarith [eq1]
    have eq4 : f x = f x * f 0 := by
      nlinarith
    exact eq4

  have h2 : f 0 = 0 ∨ f 0 = 1 := by
    have h_eq := h 0 0
    have h_eq2 : f 0 + f 0 = 2 * f 0 * f 0 := by
      norm_num at h_eq ⊢
      linarith [h_eq]
    have h_eq3 : f 0 * (f 0 - 1) = 0 := by
      linarith [h_eq2]
    cases (mul_eq_zero.1 h_eq3) with
    | inl h_eq4 =>
      left
      linarith
    | inr h_eq5 =>
      right
      linarith

  cases h2 with
  | inl h20 =>
    have h3 : ∀ x, f x = 0 := by
      intro x
      have eq1 := h1 x
      rw [h20] at eq1
      nlinarith
    unfold Even
    use (fun _ => (0 : ℝ))
    funext x
    simp [h3]
  | inr h21 =>
    have h4 : ∀ x, f x = f (-x) := by
      intro x
      have eq1 := h (-x) x
      have eq2 : f (-x) + f x = 2 * f (0 : ℝ) * f (-x) := by
        have eq3 : f (-x) + f x = 2 * f ((-x + x) / 2) * f ((-x - x) / 2) := by
          linarith [eq1]
        have h11 : (-x + x : ℝ) / 2 = (0 : ℝ) := by ring
        have h12 : (-x - x : ℝ) / 2 = (-x : ℝ) := by ring
        rw [h11, h12] at eq3
        linarith [eq3]
      have eq3 : f (-x) + f x = 2 * f (-x) := by
        rw [show f (0 : ℝ) = 1 by linarith [h21]] at eq2
        linarith
      linarith
    unfold Even
    use (fun x => f x / 2)
    funext x
    simp
    all_goals 
      try linarith [h4 x]