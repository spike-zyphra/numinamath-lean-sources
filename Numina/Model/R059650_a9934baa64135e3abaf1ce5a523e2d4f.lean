import Mathlib

theorem algebra_2710 {p : Polynomial ℝ} : (∀ x y : ℝ, p.eval x * p.eval y = p.eval x + p.eval y) ↔ (∀ x, p.eval x = 0) ∨ (∀ x, p.eval x = 2) := by
  constructor
  · -- Forward direction: if $p$ satisfies the functional equation, then it's either zero or constant 2.
    intro h
    have h0 : p.eval 0 * p.eval 0 = p.eval 0 + p.eval 0 := by
      specialize h 0 0
      simpa using h
    have h1 : p.eval 0 = 0 ∨ p.eval 0 = 2 := by
      have h_eq : (p.eval 0) * (p.eval 0 - 2) = 0 := by 
        nlinarith
      cases (mul_eq_zero.mp h_eq) with
      | inl h2 => 
        left
        exact h2
      | inr h3 =>
        right
        linarith
    cases h1 with
    | inl h1 =>
      left
      intro x
      have h2 : p.eval x * p.eval 0 = p.eval x + p.eval 0 := by
        specialize h x 0 
        simpa using h
      rw [h1] at h2 
      have : p.eval x = 0 := by 
        nlinarith 
      exact this
    | inr h1 =>
      right
      intro x
      have h2 : p.eval x * p.eval 0 = p.eval x + p.eval 0 := by 
        specialize h x 0 
        simpa using h
      rw [h1] at h2 
      have h_eq : p.eval x = 2 := by 
        nlinarith 
      exact h_eq
  · -- Backward direction: if $p$ is either zero or constant 2, then it satisfies the functional equation.
    rintro (h | h)
    · -- Case where $p(x) = 0$ for all $x$.
      intro x y
      have hx : p.eval x = 0 := h x
      have hy : p.eval y = 0 := h y
      rw [hx, hy]
      all_goals norm_num
    · -- Case where $p(x) = 2$ for all $x$.
      intro x y
      have hx : p.eval x = 2 := h x
      have hy : p.eval y = 2 := h y
      rw [hx, hy]
      all_goals norm_num