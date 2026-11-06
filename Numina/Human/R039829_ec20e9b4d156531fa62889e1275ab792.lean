import Mathlib

/- For all real numbers $r$ and $s$, define the mathematical operation $\#$ such that the following conditions apply: $r\ \#\ 0 = r, r\ \#\ s = s\ \#\ r$, and $(r + 1)\ \#\ s = (r\ \#\ s) + s + 1$. What is the value of $11\ \#\ 5$? -/
theorem algebra_10200 (f : ℝ → ℝ → ℝ) (hf1 : ∀ r, f r 0 = r) (hf2 : ∀ r s, f r s = f s r) (hf3 : ∀ r s, f (r + 1) s = f r s + s + 1) : f 11 5 = 71 := by
  -- We generalize the problem
  -- We prove that for all natural numbers $a$ and $b$, $f(a, b) = a \cdot b + a + b$
  have H (a b : ℕ) : f a b = a * b + a + b := by
    -- We do induction on $a$
    induction a
    case zero =>
      -- Base case: $a = 0$
      -- hf2 tells us that $f(0, b) = f(b, 0)$ and hf1 tells us that $f(b, 0) = b$
      simp
      rw [hf2, hf1]
    case succ a ih =>
      -- Inductive step: $a = a + 1$
      -- We use hf3 to simplify $f(a + 1, b)$
      -- Then apply the inductive hypothesis
      simp
      rw [hf3, ih]
      -- Ring identity
      ring

  -- We apply the lemma to $11$ and $5$
  change f (11 : ℕ) (5 : ℕ) = 71
  rw [H]
  norm_num
