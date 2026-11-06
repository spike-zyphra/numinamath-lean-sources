import Mathlib

/- Find all real numbers a for which there exists a non-constant function $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying the following two equations for all $x \in \mathbb{R}$ :
i) $\quad f(a x)=a^{2} f(x)$ and

ii) $f(f(x))=a f(x)$. -/
theorem algebra_605902 :
  {a : ℝ | ∃ f : ℝ → ℝ, (∀ x, f (a * x) = a ^ 2 * f x) ∧
      (∀ x, f (f x) = a * f x) ∧ ¬(∃ c, ∀ x, f x = c)} =
    {0, 1} := by
  ext a
  simp
  constructor
  -- First, we verify that a = 0 and a = 1 are solutions.
  swap
  . rintro (rfl | rfl)
    . -- Case a = 0
      -- We define a function f that takes the value 1 for negative x and 0 for non-negative x.
      use fun x ↦ if x < 0 then 1 else 0
      simp
      -- The first equation is solved by the simp tactic.
      constructor
      . -- The second equation is solved by checking both cases.
        intro x
        split_ifs <;> simp
      . -- f is not constant because f(0) = 1 and f(-1) = 0.
        intro a
        by_contra! h
        have h1 := h 0
        have h2 := h (-1)
        simp at h1 h2
        linarith only [h1, h2]
    . -- Case a = 1
      -- We define f to be the identity function.
      use fun x ↦ x
      -- Trivial verification.
      simp
      exact exists_ne
  . -- Now we show if f is a solution, then a must be 0 or 1.
    rintro ⟨f, H1, H2, H3⟩
    -- Take some x such that f(x) ≠ 0 as f is not constant.
    rcases H3 0 with ⟨x, hx⟩
    -- We can calculate f(f(f(x))) in two ways.
    -- First, f(f(f(x))) = a * f(f(x)) = a^2 * f(x)
    have h1 : f (f (f x)) = a ^ 2 * f x := by
      rw [H2, H2]
      ring
    -- Second, f(f(f(x))) = f(a * f(x)) = a^2 * f(f(x)) = a^3 * f(x)
    have h2 : f (f (f x)) = a ^ 3 * f x := by
      rw [H2 x, H1, H2]
      ring
    -- Equating the two expressions, we get a^2 * f(x) = a^3 * f(x).
    have h3 : a ^ 2 * f x = a ^ 3 * f x := by
      rwa [← h1]
    -- Dividing both sides by f(x) (which is non-zero), we get a^2 = a^3.
    simp [hx] at h3
    -- So a^2 * (a - 1) = 0.
    replace h3 : a ^ 2 * (a - 1) = 0 := by linear_combination -h3
    -- So a = 0 or a = 1.
    simp [sub_eq_zero] at h3
    exact h3
