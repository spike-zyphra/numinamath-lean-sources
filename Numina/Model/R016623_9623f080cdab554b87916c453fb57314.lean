import Mathlib

theorem algebra_92494 {a b : ℝ} (P : ℝ → ℝ) (hP : ∀ x, P x = x ^ 2 + a * x + b)
    (s t : ℝ) (hs : s ≠ t) (hST : P s = t ∧ P t = s) :
    (b - s * t) ^ 2 + a * (b - s * t) + b - s * t = 0 := by

  have h1 : s ^ 2 + a * s + b = t := by
    rw [hP s] at hST
    linarith [hST.1]

  have h2 : t ^ 2 + a * t + b = s := by
    rw [hP t] at hST
    linarith [hST.2]

  -- Subtract the two equations s^2 + a * s + b = t and t^2 + a * t + b = s
  -- s^2 + a * s + b - (t^2 + a * t + b) = t - s
  -- s^2 + a * s + b - t^2 - a * t - b = t - s
  -- s^2 - t^2 + a * (s - t) = t - s

  have eq1 : (s - t) * (s + t + a) = - (s - t) := by
    nlinarith

  have eq2 : s + t + a = -1 := by
    apply (mul_left_inj' (show s - t ≠ 0 by
      intro h
      apply hs
      linarith
    )).mp
    linarith [eq1]

  have eq3 : a = -1 - s - t := by
    linarith [eq2]

  have eq4 : b = s + t + s * t := by
    rw [eq3] at h1
    linarith [h1]

  have eq5 : b - s * t = s + t := by
    linarith [eq4]

  rw [eq5]
  rw [eq3]
  rw [eq4]
  nlinarith [sq_pos_of_ne_zero (show s - t ≠ 0 by
    intro h
    apply hs
    linarith
  )]