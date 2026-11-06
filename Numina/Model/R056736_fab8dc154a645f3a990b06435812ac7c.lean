import Mathlib

theorem algebra_8726 {f : ℝ → ℝ} : (∀ x y, x * f (x + y) = x * f x + f (x ^ 2) * f y) ↔ ∀ x, f x = 0 := by
  constructor
  · -- Assume functional Equation, prove f(x) = 0 for all x
    intro h
    have h1 : f 0 = 0 := by
      specialize h 0 0
      simp at h ⊢
      nlinarith
    have h3 : f 1 = 0 := by
      have eq1 := h 1 (-1)
      norm_num [h1] at eq1
      have eq2 := h (-1) 1
      norm_num [h1] at eq2
      have eq3 : f (-1) = (f 1) ^ 2 := by nlinarith
      have eq4 : f 1 * ( (f 1) ^ 2 + 1 ) = 0 := by
        nlinarith [eq1, eq3]
      cases (mul_eq_zero.mp eq4) with
      | inl h5 =>
        linarith
      | inr h6 =>
        have h7 : (f 1) ^ 2 + 1 = 0 := by linarith
        nlinarith [sq_nonneg (f 1)]
    -- Now, we need to prove that for all y, f(1 + y) = 0
    have h4 : ∀ y : ℝ, f (1 + y) = 0 := by
      intro y
      have eqn := h 1 y
      simp [h3] at eqn
      linarith
    intro x
    specialize h4 (x - 1)
    have h5 : 1 + (x - 1 : ℝ) = (x : ℝ) := by ring
    rw [h5] at h4
    exact h4
  · -- Assume f(x) = 0 for all x, prove functional Equation
    intro hf x y
    simp [hf]
    <;> ring