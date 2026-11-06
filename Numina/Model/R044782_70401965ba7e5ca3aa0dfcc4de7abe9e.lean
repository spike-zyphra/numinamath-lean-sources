import Mathlib

theorem algebra_123092 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) + f (x - 1) = Real.sqrt 2 * f x) :
    ∃ c > 0, Function.Periodic f c := by
  have eq1 : ∀ x, f (x + 2) = Real.sqrt 2 * f (x + 1) - f x := by
    intro x
    have eq2 := h (x + 1)
    have eq3 := h x
    have eq4 : f ((x + 1) + 1) + f ((x + 1) - 1) = Real.sqrt 2 * f (x + 1) := by
      simpa using eq2
    have eq5 : f (x + 2) + f x = Real.sqrt 2 * f (x + 1) := by
      have h1 : (x + 1) + 1 = x + 2 := by ring
      have h2 : (x + 1) - 1 = x := by ring
      rw [h1, h2] at eq4
      linarith
    linarith

  have eq2 : ∀ x, f (x + 4) = - f x := by
    intro x
    have eq3 : f (x + 3) = Real.sqrt 2 * f (x + 2) - f (x + 1) := by
      specialize eq1 (x + 1)
      have h1 : (x + 1) + 2 = x + 3 := by ring
      have h2 : (x + 1) + 1 = x + 2 := by ring
      rw [h1] at eq1
      rw [h2] at eq1
      linarith

    have eq4 : f (x + 4) = Real.sqrt 2 * f (x + 3) - f (x + 2) := by
      specialize eq1 (x + 2)
      have h1 : (x + 2) + 2 = x + 4 := by ring
      have h2 : (x + 2) + 1 = x + 3 := by ring
      rw [h1] at eq1
      rw [h2] at eq1
      linarith

    rw [eq4, eq3]
    have eq5 : Real.sqrt 2 * (Real.sqrt 2 * f (x + 2) - f (x + 1)) - f (x + 2) = - f x := by
      have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      calc
        Real.sqrt 2 * (Real.sqrt 2 * f (x + 2) - f (x + 1)) - f (x + 2)
          = (Real.sqrt 2 ^ 2 * f (x + 2) - Real.sqrt 2 * f (x + 1)) - f (x + 2) := by ring
        _ = (2 * f (x + 2) - Real.sqrt 2 * f (x + 1)) - f (x + 2) := by 
          rw [h6]
        _ = f (x + 2) - Real.sqrt 2 * f (x + 1) := by ring
        _ = (Real.sqrt 2 * f (x + 1) - f x) - Real.sqrt 2 * f (x + 1) := by 
          rw [eq1 x]
        _ = - f x := by ring

    linarith [eq5]

  have eq3 : ∀ x, f (x + 8) = f x := by
    intro x
    have eq4 : f (x + 4) = - f x := eq2 x
    have eq5 : f (x + 8) = - f (x + 4) := by
      have eq6 : f (x + 4 + 4) = - f (x + 4) := eq2 (x + 4)
      have h10 : x + 4 + 4 = x + 8 := by ring
      rw [h10] at eq6
      linarith

    rw [eq5, eq4]
    all_goals ring

  use 8
  constructor
  · norm_num
  · unfold Function.Periodic
    intro x
    specialize eq3 x
    linarith