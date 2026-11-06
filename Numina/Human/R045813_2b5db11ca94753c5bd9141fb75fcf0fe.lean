import Mathlib
/- 5. Let $R$ be the set of all real numbers. Find all functions $f: \mathbf{R} \rightarrow \mathbf{R}$, such that for any real numbers $x, y$, we have
$$
\begin{array}{c}
f(x+f(x+y))+f(x y) \\
=x+f(x+y)+y f(x) .
\end{array}
$$ -/
theorem algebra_310914 : {f : ℝ → ℝ | ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x} = {fun x => x, fun x => 2 - x}:= by
  ext f
  constructor
  -- Forward direction: If f satisfies the functional equation, then f(x) = x or f(x) = 2-x
  .
    intro h
    simp at h
    -- Setting y = 1 in the functional equation gives us a useful identity
    have h1 : ∀ x : ℝ, f (x + f (x + 1)) = x + f (x + 1):= by
      intro x
      specialize h x 1
      simp at h
      exact h
    -- Case analysis based on whether f(0) = 0 or f(0) ≠ 0
    by_cases h2 : f 0 ≠ 0
    -- Case 1: f(0) ≠ 0, we'll show f(x) = 2-x
    .
      simp
      right
      funext x
      specialize h 0 (x - 1 + f x)
      simp at h
      specialize h1 (x - 1)
      rw [show x - 1 + 1 = x by ring] at h1
      rw [h1] at h
      rw [h1] at h
      replace h : (f x + x - 2) * f 0 = 0:= by linarith
      simp [h2] at h
      linarith
    -- Case 2: f(0) = 0, we'll show f(x) = x
    .
      left
      funext x
      simp at h2
      -- First establish that f(-1) = -1
      have h3 : f (-1) = -1:= by
        specialize h1 (-1)
        simp at h1
        rw [h2] at h1
        simp at h1
        exact h1
      -- Next establish that f(1) = 1
      have h4 : f 1 = 1:= by
        specialize h 1 (-1)
        simp at h
        rw [h2, h3] at h
        simp at h
        linarith
      -- Derive another useful identity by setting x = 1
      have h5 : ∀ y : ℝ, f (1 + f (y + 1)) + f y = 1 + f (y + 1) + y:= by
        intro y
        specialize h 1 y
        simp at h
        rw [h4] at h
        rw [show 1 + y = y + 1 by ring] at h
        linarith
      -- Another identity by setting y = 0
      have h6 : ∀ x : ℝ, f (x + f (x + 1) + 1) = x + f (x + 1) + 1:= by
        intro x
        specialize h (x + 1) 0
        simp at h
        rw [h2] at h
        ring_nf at h ⊢
        exact h
      -- If f(y) = y and f(y+1) = y+1, then f(y+2) = y+2
      replace h5 : ∀ y : ℝ, f y = y → f (y + 1) = y + 1 → f (y + 2) = y + 2:= by
        intro y hy1 hy2
        specialize h5 y
        rw [hy1, hy2] at h5
        ring_nf at h5 ⊢
        linarith
      -- Another identity derived from previous results
      replace h5 : ∀ x : ℝ, f (x + f (x + 1) + 2) = x + f (x + 1) + 2:= by
        intro x
        specialize h1 x
        specialize h6 x
        exact h5 (x + f (x + 1)) h1 h6
      -- Proving f(-x) = -f(x) for all x
      have h7 : ∀ x : ℝ, f (-x) = -f x:= by
        intro x
        specialize h5 (x - 2)
        ring_nf at h5
        rw [show -1 + x = x + -1 by ring] at h5
        specialize h x (-1)
        simp at h
        linarith
      -- Final steps to prove f(x) = x
      have h8:= h 1 x
      simp at h8
      rw [h4] at h8
      simp at h8
      specialize h (-1) (-x)
      simp at h
      rw [h3] at h
      simp at h
      rw [show -1 + -x = -(x + 1) by ring] at h
      rw [h7 (x + 1)] at h
      rw [show -1 + -f (x + 1) = - (1 + f (x + 1)) by ring] at h
      rw [h7 (1 + f (x + 1))] at h
      rw [show 1 + x = x + 1 by ring] at h8
      linarith
  -- Backward direction: Verify that both f(x) = x and f(x) = 2-x satisfy the functional equation
  .
    intro h
    simp at h
    rcases h with h | h
    all_goals
      subst f
      simp
      intro x y
      linarith
