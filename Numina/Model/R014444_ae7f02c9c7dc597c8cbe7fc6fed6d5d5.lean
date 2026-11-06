import Mathlib

theorem algebra_234986 {A B S : ℝ} (h₀ : A < B) (h₁ : S ∈ Set.Icc A B)
    (h₂ : ∃ x y, x > 0 ∧ y > 0 ∧ x + y = B - A ∧ |x - y| = 8 ∧ x = (y / 3)) :
    B - A = 16 := by
  rcases h₂ with ⟨x, y, hx, hy, h_eq1, h_eq2, h_eq3⟩
  have h4 : x - y = 8 ∨ x - y = -8 := by
    cases eq_or_eq_neg_of_abs_eq h_eq2 with
    | inl h1 =>
      left
      linarith
    | inr h2 =>
      right
      linarith
  cases h4 with
  | inl h4 =>
    -- We have x - y = 8.
    -- Substitute x = y / 3 (from h_eq3) into the equation.
    -- (y / 3) - y = 8
    -- y/3 - 3y/3 = -2y/3 = 8
    -- Multiply both sides by 3: -2y = 24 => y = -12
    -- Contradicts with hy: y > 0
    have h5 : y = -12 := by
      linarith [h_eq3, h4]
    have h6 : y > 0 := hy
    linarith
  | inr h4 =>
    -- We have x - y = -8.
    -- Substitute x = y / 3 (from h_eq3) into the equation.
    -- (y / 3) - y = -8
    -- y/3 - 3y/3 = -2y/3 = -8
    -- Multiply both sides by 3: -2y = -24 => y = 12
    have h7 : y = 12 := by
      linarith [h_eq3, h4]
    -- Then x = y / 3 = 12 / 3 = 4
    have h8 : x = 4 := by
      linarith [h_eq3, h7]
    -- Substitute x and y into the equation x + y = B - A
    -- B - A = 4 + 12 = 16
    have h9 : B - A = 16 := by
      linarith [h_eq1, h7, h8]
    linarith