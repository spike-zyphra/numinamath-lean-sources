import Mathlib

theorem algebra_7509 (f : ℝ → ℝ) :
    (∀ x y, f x * f y - f x = x * y + f (y + 1)) ↔
    ∀ x, f x = 1 - x := by
  constructor
  · -- Assume functional equation, prove f(x) = 1 - x
    intro h
    have h1 : ∀ x y : ℝ, f x * f y - f x = x * y + f (y + 1) := h
    have h2 := h1 0 0
    have h3 := h1 1 0
    have h4 := h1 0 1
    have h5 := h1 1 1
    have h6 := h1 2 0
    -- For all x, f(x) * (f(0) - 1) = f(1)
    have h7 : ∀ x : ℝ, f x * (f 0 - 1) = f 1 := by
      intro x
      specialize h1 x 0
      simp at h1 ⊢
      linarith
    -- Let's consider f(0) - 1 = 0 ⇒ f(0) = 1.
    by_cases h10 : f 0 - 1 = 0
    · -- Suppose f(0) - 1 = 0. Then f(0) = 1.
      have f0 : f 0 = 1 := by linarith
      -- From h7: ∀ x, f x * 0 = f 1 ⇒ f 1 = 0.
      have f1 : f 1 = 0 := by
        specialize h7 1
        rw [show f 0 - 1 = 0 by linarith] at h7
        linarith
      -- Now, need to show ∀ x, f x = 1 - x
      intro x
      have eq1 := h1 x 0
      simp [f0, f1] at eq1
      have eq2 := h1 0 x
      simp [f0, f1] at eq2
      have eq3 := h1 x 1
      simp [f0, f1] at eq3
      have eq4 := h1 1 x
      simp [f0, f1] at eq4
      have eq5 := h1 (x - 1) 1
      simp [f0, f1] at eq5
      -- Solving these equations using linarith
      have eq6 : f x = 1 - x := by
        nlinarith [sq_nonneg (f x - (1 - x)), sq_nonneg (f (x + 1) - ( -x - 0)), sq_nonneg (f 0 -1 ), sq_nonneg (f 1 -0 ), sq_nonneg (f (x -1 ) - ( -x ))]
      exact_mod_cast eq6
    · -- Case f(0) - 1 ≠ 0
      have h9 := h7 1
      have eq7 : f 1 * (f 0 - 2 ) = 0 := by
        have eq8 : f 1 = f 1 := by rfl
        nlinarith [h9, sq_pos_of_ne_zero (show f 0 - 1 ≠ 0 by intro h'; apply h10; linarith)]
      cases' (mul_eq_zero.mp eq7) with h15 h16
      · -- So f 1 = 0 as contradiction since here
        exfalso
        have h16 := h7 2
        nlinarith [sq_pos_of_ne_zero (show f 0 - 1 ≠ 0 by intro h'; apply h10; linarith)]
      · -- So f 0 - 2 = 0, a contradiction as from here
        exfalso
        have h10' : f 0 - 1 = 0 := by
          nlinarith
        tauto
  · -- Assume f(x) = 1 - x for all x, prove the functional equation
    intro hf x y
    rw [hf x, hf y, hf (y + 1)]
    ring