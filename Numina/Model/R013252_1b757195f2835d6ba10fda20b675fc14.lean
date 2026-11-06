import Mathlib

theorem algebra_200548 {f : ℤ → ℤ → ℤ} (h1 : ∀ x, f x 0 = x)
    (h2 : ∀ x y, f x (y - 1) = f x y - 2) (h3 : ∀ x y, f x (y + 1) = f x y + 2) :
    f (-673) (-673) = -2019 := by

  have h4 : ∀ x y, f x y = x + 2 * y := by
    intro x y
    have eq1 : ∀ (y : ℤ), f x y = x + 2 * y := by
      intro y
      induction y using Int.induction_on with
      | hz =>
        simp [h1 x]
      | hp i hi =>
        have eq2 : f x (i + 1) = f x i + 2 := by
          specialize h3 x i
          linarith 
        rw [eq2]
        rw [hi]
        all_goals ring
      | hn i hi =>
        have eq7 : f x (-↑i - 1) = x + 2 * (-↑i - 1) := by
          have eq13 : f x (-↑i - 1) = f x (-↑i) - 2 := by
            specialize h2 x (-↑i)
            simpa using h2
          have eq14 : f x (-↑i) = x + 2 * (-↑i) := by
            simpa using hi 
          rw [eq14] at eq13
          linarith
        simpa using eq7
    specialize eq1 y
    simpa using eq1

  have h5 : f (-673) (-673) = -673 + 2 * (-673) := by
    apply h4

  rw [h5]
  all_goals norm_num