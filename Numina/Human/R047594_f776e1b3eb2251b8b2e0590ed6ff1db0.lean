import Mathlib
/- Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function satisfying $f(x) f(y)=f(x-y)$. Find all possible values of $f(2017)$. -/
theorem algebra_609640 : {a : ℝ | ∃ f : ℝ → ℝ, (∀ x y : ℝ, f x * f y = f (x - y)) ∧ f 2017 = a} = {0, 1} := by
  ext a
  constructor
  -- Forward direction: proving that if such a function exists, f(2017) must be 0 or 1
  .
    intro h
    simp
    simp at h
    rcases h with ⟨f, hf, h1⟩
    rw [←h1]
    -- First, consider f(0)f(0) = f(0)
    replace h1:= hf 0 0
    simp at h1
    -- This implies f(0)(f(0) - 1) = 0
    replace h1 : f 0 * (f 0 - 1) = 0:= by linarith
    simp at h1
    rcases h1 with h1 | h1
    -- Case 1: If f(0) = 0, then f(2017) = 0
    .
      left
      specialize hf 2017 2017
      simp at hf
      rw [h1] at hf
      simp at hf
      exact hf
    -- Case 2: If f(0) = 1, then f(2017) = 1
    .
      replace h1 : f 0 = 1:= by linarith
      -- Prove that f is even: f(x) = f(-x)
      have h2 : ∀ x : ℝ, f x = f (-x):= by
        intro x
        specialize hf 0 x
        simp at hf
        rw [h1] at hf
        simp at hf
        exact hf
      -- Prove that f(x+y) = f(x-y)
      have h3 : ∀ x y : ℝ, f (x + y) = f (x - y):= by
        intro x y
        have g1:= hf x y
        have g2:= hf x (-y)
        simp at g1 g2
        rw [h2 y] at g1
        linarith
      right
      specialize h3 (2017 / 2) (2017 / 2)
      ring_nf at h3
      linarith
  -- Backward direction: proving that 0 and 1 are indeed possible values
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case 1: Construct constant function f(x) = 0
    .
      simp
      use fun _ => 0
      subst a
      simp
    -- Case 2: Construct constant function f(x) = 1
    .
      simp
      use fun _ => 1
      subst a
      simp
