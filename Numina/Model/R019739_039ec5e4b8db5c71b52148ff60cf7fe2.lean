import Mathlib

theorem algebra_31578 {f : ℝ → ℝ → ℝ → ℤ} (h : ∀ x y z, f x y z + f x z y + f y x z + f z y x = 0)
    (a b c : ℤ) : Even (f a b c) := by
  have h1 := h (a : ℝ) (b : ℝ) (c : ℝ)
  -- Apply the relation to a, c, b.
  -- We get: f(a, c, b) + f(a, b, c) + f(c, a, b) + f(b, c, a) = 0
  have h2 := h (a : ℝ) (c : ℝ) (b : ℝ)
  -- Apply the relation to b, a, c.
  -- We get: f(b, a, c) + f(b, c, a) + f(a, b, c) + f(c, a, b) = 0
  have h3 := h (b : ℝ) (a : ℝ) (c : ℝ)
  -- Apply the relation to b, c, a.
  -- We get: f(b, c, a) + f(b, a, c) + f(c, b, a) + f(a, c, b) = 0
  have h4 := h (b : ℝ) (c : ℝ) (a : ℝ)
  -- Apply the relation to c, a, b.
  -- We get: f(c, a, b) + f(c, b, a) + f(a, c, b) + f(b, a, c) = 0
  have h5 := h (c : ℝ) (a : ℝ) (b : ℝ)
  -- Apply the relation to c, b, a.
  -- We get: f(c, b, a) + f(c, a, b) + f(b, c, a) + f(a, b, c) = 0
  have h6 := h (c : ℝ) (b : ℝ) (a : ℝ)
  -- To prove that f(a,b,c) is even, we need to show that f(a,b,c) ≡ 0 (mod 2)
  simp at h1 h2 h3 h4 h5 h6
  -- These equations form a system where each term is related by the group algebra. Adding them up with some prime coefficients must result in f(a,b,c) being even, which the omega tactic can solve.
  have h7 : (f a b c : ℤ) % 2 = 0 := by
    omega
  -- Now that we have proven f(a,b,c) ≡ 0 (mod 2), we can rewrite it into Lean's divisibility.
  exact ⟨f a b c / 2, by omega⟩