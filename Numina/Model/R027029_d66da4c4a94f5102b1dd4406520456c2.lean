import Mathlib

theorem algebra_84061 {f : ℝ → ℝ} (h : ∀ x, f x + x * f (1 - x) = x ^ 2) :
    ∃ g, ∀ x, f x = g x ∧ g = fun x => (x ^ 3 - 3 * x ^ 2 + x) / (x - x ^ 2 - 1) := by
  use fun x => (x ^ 3 - 3 * x ^ 2 + x) / (x - x ^ 2 - 1)
  intro x
  constructor
  · -- Show that f x = g x
    have eq1 := h x
    have eq2 := h (1 - x)
    simp [show 1 - (1 - x) = x by ring] at eq2
    have eq3 : f x = (x ^ 3 - 3 * x ^ 2 + x) / (x - x ^ 2 - 1) := by
      have eq4 : f x + x * f (1 - x) = x ^ 2 := by
        simpa using eq1
      have eq5 : f (1 - x) + (1 - x) * f x = (1 - x) ^ 2 := by
        simpa using eq2
      -- Solve the system of equations
      have eq6 : f (1 - x) = (1 - x) ^ 2 - (1 - x) * f x := by
        linarith
      rw [eq6] at eq4
      have eq7 : (x - x ^ 2 - 1) ≠ 0 := by
        by_contra h1
        have h2 : x ^ 2 - x + 1 = 0 := by nlinarith
        nlinarith [sq_nonneg (x - 1 / 2)]
      have eq8 : f x * (x^2 - x + 1) = -x^3 + 3 * x^2 - x := by
        nlinarith [sq_nonneg (x^2 - x + 1), sq_nonneg (x - (1 - x)), sq_nonneg (f x - f (1 - x))]
      have h9 : x - x ^ 2 - 1 = - (x ^ 2 - x + 1) := by
        ring
      have h11 : f x = ( -x^3 + 3 * x^2 - x ) / (x^2 - x + 1 ) := by
        have h9 : x ^ 2 - x + 1 ≠ 0 := by
          intro h'
          have h2 : x ^ 2 - x + 1 = 0 := by nlinarith
          nlinarith [sq_nonneg (x - 1 / 2)]
        have eq9 : f x * (x^2 - x + 1) = -x^3 + 3 * x^2 - x := by
          nlinarith
        field_simp [h9] at *
        nlinarith
      rw [show (x ^ 3 - 3 * x ^ 2 + x) / (x - x ^ 2 - 1) = ( -x^3 + 3 * x^2 - x ) / (x^2 - x + 1 ) by
        have h9 : x - x ^ 2 - 1 = - (x ^ 2 - x + 1) := by
          ring
        rw [h9]
        rw [div_neg]
        <;> ring_nf
      ]
      rw [h11]
    simpa using eq3
  · -- Show that g = ...
    all_goals
      rfl