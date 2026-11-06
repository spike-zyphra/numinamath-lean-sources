import Mathlib

theorem algebra_205764 {f : ℝ → ℝ} (h : ∀ x, f x + x * f (2 - x) = 3 * x - x ^ 2) :
    ∀ x, f x = x := by
  intro x
  have eq1 := h x
  have eq2 := h (2 - x)
  simp [show 2 - (2 - x : ℝ) = x by ring] at eq2
  ring_nf at eq1 eq2
  by_cases h1 : x - 1 = 0
  · -- x - 1 = 0, so x = 1
    have hx : x = 1 := by linarith
    rw [hx]
    have eq1_1 := h 1
    norm_num at eq1_1 ⊢
    all_goals linarith
  · -- x - 1 ≠ 0
    have eq3 : f x * (x - 1) ^ 2 = x * (x - 1) ^ 2 := by
      nlinarith [sq_nonneg (f x - x), sq_nonneg (f (2 - x) - (2 - x)), sq_nonneg (x - 1)]
    have h1' : (x - 1 : ℝ) ≠ 0 := h1
    have h2 : f x = x := by
      apply (mul_left_inj' (show (x - 1 : ℝ) ^ 2 ≠ 0 by
        have h1' : (x - 1 : ℝ) ≠ 0 := h1
        intro h
        have : x - 1 = 0 := by
          have h' : (x - 1) ^ 2 = 0 := by
            nlinarith
          have : x - 1 = 0 := by
            nlinarith
          assumption
        contradiction
      )).mp
      linarith
    exact h2