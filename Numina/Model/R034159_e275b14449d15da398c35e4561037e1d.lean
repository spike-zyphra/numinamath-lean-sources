import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_188100 (f : ℝ → ℝ) (hf : f = λ x => exp (2*x^2 - 4*x - 6)) :
    IsGreatest (image f (Icc 0 3)) (f 3) ∧ IsLeast (image f (Icc 0 3)) (f 1) := by
  have h7 : f 3 = (1 : ℝ) := by
    rw [hf]
    norm_num

  have h8 : f 1 = exp (-8 : ℝ) := by
    rw [hf]
    norm_num

  constructor
  · -- Show that $f(3)$ is the greatest element in the image of $f$ on $[0, 3]$
    constructor
    · -- Show that $f 3 \in \text{image } f (Icc 0 3)$
      use 3
      constructor
      · -- Show that 3 ∈ Icc 0 3
        norm_num
      · -- Show that f 3 = f 3
        rfl
    · -- Show that $f 3$ is the greatest element
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have h9 : f x = exp (2 * x^2 - 4 * x - 6) := by
        rw [hf]
      have h10 : 2 * x ^ 2 - 4 * x - 6 ≤ (0 : ℝ) := by
        nlinarith [sq_nonneg (x - 3), hx.1, hx.2]
      have h11 : exp (2 * x^2 - 4 * x - 6) ≤ exp (0 : ℝ) := by
        apply Real.exp_le_exp_of_le
        linarith [h10]
      have h12 : exp (0 : ℝ) = (1 : ℝ) := by
        simp
      have h13 : f x ≤ f 3 := by
        have eq1 : exp (2 * x^2 -4 *x -6) ≤ (1 : ℝ) := by
          linarith [h11, h12]
        have eq2 : f x = exp (2 * x^2 -4 *x -6) := by
          linarith [h9]
        have eq3 : f 3 = (1 : ℝ) := by
          linarith [h7]
        linarith [eq1, eq2, eq3]
      linarith [h13, h7]
  · -- Show that $f(1)$ is the least element in the image of $f$ on $[0, 3]$
    constructor
    · -- Show that $f 1 \in \text{image } f (Icc 0 3)$
      use 1
      constructor
      · -- Show that 1 ∈ Icc 0 3
        norm_num
      · -- Show that f 1 = f 1
        rfl
    · -- Show that $f 1$ is the least element
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have h9 : f x = exp (2 * x^2 - 4 * x - 6) := by
        rw [hf]
      have h14 : -8 ≤ (2 * x^2 - 4 *x -6 : ℝ) := by
        nlinarith [sq_nonneg (x - 1), hx.1, hx.2]
      have h15 : exp (-8 : ℝ) ≤ exp (2 *x^2 -4 *x -6 : ℝ) := by
        apply Real.exp_le_exp_of_le
        linarith [h14]
      have h16 : f 1 ≤ f x := by
        have eq1 : exp (-8 : ℝ) ≤ exp (2 *x^2 -4 *x -6 : ℝ) := h15
        have eq2 : f 1 = exp (-8 : ℝ) := by
          linarith [h8]
        have eq3 : f x = exp (2 *x^2 -4 *x -6 : ℝ) := by
          linarith [h9]
        linarith [eq1, eq2, eq3]
      linarith [h16, h8]