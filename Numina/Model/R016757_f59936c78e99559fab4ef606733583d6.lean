import Mathlib

theorem algebra_8782 {f : ℝ → ℝ} (h : ∀ x y, f (x + f y) = 2 * x + 2 * f (y + 1)) :
  ∀ x, f x = 2 * x + 4 := by
  -- Prove that $f(f(y)) = 2f(y + 1)$ for all $y$ by setting $x = 0$ in the original equation.
  have h1 : ∀ y, f (f y) = 2 * f (y + 1) := by
    intro y
    specialize h 0 y
    norm_num at h
    simpa using h

  -- For all $x$, $f(x + f 0) = 2x + 2f 1$ by setting $y = 0$ in the original equation.
  have h2 : ∀ x, f (x + f 0) = 2 * x + 2 * f 1 := by
    intro x
    specialize h x 0
    simpa using h
  
  -- Express $f(z)$ as $2z + k$ for some constant $k = 2f 1 - 2f 0$.
  have h3 : ∀ z, f z = 2 * z + (2 * f 1 - 2 * f 0) := by
    intro z
    have eq1 := h2 (z - f 0)
    have h4 : (z - f 0) + f 0 = z := by ring
    rw [h4] at eq1
    linarith
  
  -- Prove that $k = 4$, i.e., $2f 1 - 2f 0 = 4$.
  have eq4 : 2 * f 1 - 2 * f 0 = 4 := by
    -- From $f(f y) = 2f (y + 1)$, we compute both sides using $f z = 2z + k$.
    have eq1 : ∀ y, f (f y) = 4 * y + 3 * (2 * f 1 - 2 * f 0) := by
      intro y
      have eq5 : f (f y) = f (2 * y + (2 * f 1 - 2 * f 0)) := by
        have eq6 : f y = 2 * y + (2 * f 1 - 2 * f 0) := by
          apply h3
        rw [eq6]
        <;> ring_nf
      rw [eq5]
      have eq6 : f (2 * y + (2 * f 1 - 2 * f 0)) = 2 * (2 * y + (2 * f 1 - 2 * f 0)) + (2 * f 1 - 2 * f 0) := by
        apply h3
      rw [eq6]
      all_goals ring_nf
  
    -- Similarly compute $2f(y+1)$.
    have eq2 : ∀ y, 2 * f (y + 1) = 4 * y + 4 + 2 * (2 * f 1 - 2 * f 0) := by
      intro y
      have eq7 : f (y + 1) = 2 * (y + 1) + (2 * f 1 - 2 * f 0) := by
        apply h3
      have eq8 : f (y + 1) = 2 * (y + 1) + (2 * f 1 - 2 * f 0) := eq7
      calc
        2 * f (y + 1) = 2 * (2 * (y + 1) + (2 * f 1 - 2 * f 0)) := by rw [eq8]
        _ = 4 * (y + 1) + 2 * (2 * f 1 - 2 * f 0) := by ring_nf
        _ = 4 * y + 4 + 2 * (2 * f 1 - 2 * f 0) := by ring_nf
  
    -- Use $f(f y) = 2f(y+1)$ to equate and solve.
    have eq3 := h1 0
    have eq5 := eq1 0
    have eq6 := eq2 0
    norm_num at eq5 eq6 eq3 
    linarith

  -- Prove the final result using $f z = 2z + k$ and $k = 4$.
  intro x
  have eq7 : f x = 2 * x + (2 * f 1 - 2 * f 0) := h3 x
  rw [eq7]
  have eq8 : (2 * f 1 - 2 * f 0) = 4 := eq4
  linarith [eq8]