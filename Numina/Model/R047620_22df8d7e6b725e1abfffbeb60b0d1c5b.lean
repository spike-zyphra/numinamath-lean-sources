import Mathlib

theorem algebra_227421 :
    ¬∃ f : ℝ → ℝ, ∀ x, f (1 + f x) = 1 - x ∧ f (f x) = x := by 
  intro h
  rcases h with ⟨f, hf⟩
  have eq1 := hf 0
  have eq2 := hf 1
  have eq3 := hf (f 0)
  have eq4 := hf (f 1)
  -- From `eq1`:
  -- `f (1 + f 0) = 1 - 0` simplifies to `f (1 + f 0) = 1`.
  -- `f (f 0) = 0`.
  have h1 : f (1 + f 0) = 1 := by 
    linarith [eq1.1]
  have h2 : f (f 0) = 0 := by 
    linarith [eq1.2]
  -- From `eq3` (x = f 0):
  -- `f (1 + f (f 0)) = 1 - f 0`. Substituting `f (f 0) = 0` (from `h2` into this expression). 
  -- `f (1 + 0) = 1 - f 0`. This simplifies to `f 1 = 1 - f 0`.
  have h3 : f 1 = 1 - f 0 := by
    have eq5 := eq3.1
    have eq6 : 1 + f (f 0) = (1 : ℝ) := by
      have h7 : f (f 0) = 0 := h2
      linarith 
    rw [eq6] at eq5
    linarith
  -- From `eq2` (x=1):
  -- `f (1 + f 1) = 1 - 1 = 0`.
  -- `f (f 1) = 1`.
  have h4 : f (1 + f 1) = 0 := by
    linarith [eq2.1]
  have h5 : f (f 1) = 1 := by
    linarith [eq2.2]
  -- From `eq4` (x = f 1):
  -- `f (1 + f (f 1)) = 1 - f 1`. From `h5`, `f (f 1) = 1`. So `f (1 + 1) = 1 - f 1`. This simplifies to `f 2 = 1 - f 1`.
  have h8 : f 2 = 1 - f 1 := by
    have eq7 := eq4.1
    have eq8 : 1 + f (f 1) = (2 : ℝ) := by
      have h7 : f (f 1) = 1 := h5
      linarith 
    rw [eq8] at eq7
    linarith
  -- We can express $f 2$ in terms of $f 0$.
  -- From `h3 : f 1 = 1 - f 0`.
  -- From `h8 : f 2 = 1 - f 1`. Substituting `f 1 = 1 - f 0` into this gives `f 2 = f 0$.
  have h9 : f 2 = f 0 := by 
    have eq10 : f 2 = 1 - f 1 := h8
    have eq11 : f 1 = 1 - f 0 := h3
    linarith [eq10, eq11]
  -- From `eq8 : f (f 2) = 2`.
  -- From `h9 : f 2 = f 0`.
  -- Substituting, we get $f(f0) = 2$.
  have eq10 : f (f 0) = 2 := by
    have eq11 : f 2 = f 0 := h9
    have eq9 : f (f 2) = 2 := by
      have eq62 := hf 2
      linarith [eq62.2]
    rw [eq11] at eq9
    linarith
  -- This contradicts `h2 : f (f 0) = 0`.
  linarith [h2, eq10]