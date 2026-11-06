import Mathlib

/- Lemma: The equation in the problem is equivalent to the quadratic equation $2x^2 - 2x + 4 = a$, with additional conditions $x \neq 0$ and $x \neq 2$. -/
lemma lemma_1 {x : ℝ} : x ≠ 0 ∧ x ≠ 2 ∧ x / (x - 2) + (x - 2) / x = (a - 2 * x) / (x ^ 2 - 2 * x) ↔ x ≠ 0 ∧ x ≠ 2 ∧ 2 * x ^ 2 - 2 * x + 4 - a = 0 := by
  -- Rewrite $x^2 - 2x$ in linear factors.
  rw [show x ^ 2 - 2 * x = (x - 2) * x by ring]
  constructor
  . rintro ⟨h₁, h₂, h₃⟩
    -- Cancel the denominator.
    field_simp [sub_ne_zero.mpr h₂] at h₃
    exact ⟨h₁, h₂, by linear_combination h₃⟩
  . rintro ⟨h₁, h₂, h₃⟩
    -- Cancel the denominator.
    field_simp [sub_ne_zero.mpr h₂]
    exact ⟨h₁, h₂, by linear_combination h₃⟩

/- 3. A. Given the equation in terms of $x$
$$
\frac{x}{x-2}+\frac{x-2}{x}=\frac{a-2 x}{x^{2}-2 x}
$$

has exactly one real root. Then the number of real values of $a$ that satisfy this condition is ( ).
(A) 1
(B) 2
(C) 3
(D) 4 -/
theorem algebra_311348 :
    {a : ℝ | ∃! x, x ≠ 0 ∧ x ≠ 2 ∧ x / (x - 2) + (x - 2) / x = (a - 2 * x) / (x ^ 2 - 2 * x)}.encard = 3 := by
  -- We compute the set of $a$ that satisfy the equation to be $\{\frac{7}{2}, 4, 8\}$. So the number of real values of $a$ that satisfy this condition is 3.
  suffices {a : ℝ | ∃! x, x ≠ 0 ∧ x ≠ 2 ∧ x / (x - 2) + (x - 2) / x = (a - 2 * x) / (x ^ 2 - 2 * x)} = {7 / 2, 4, 8} by
    refine Set.encard_eq_three.mpr ⟨7 / 2, 4, 8, ?_⟩
    norm_num [this]
  ext a
  simp [lemma_1]
  constructor
  -- We first prove that $\frac{7}{2}, 4, 8$ are solutions.
  swap
  . rintro (rfl | rfl | rfl)
    -- For $\frac{7}{2}$, we can find $x = \frac{1}{2}$ that satisfies the equation.
    . use 1 / 2
      norm_num
      intro y hy₁ hy₂ h
      -- Factorize the equation.
      replace h : 2 * (y - 1 / 2) ^ 2 = 0 := by linear_combination h
      simpa [sub_eq_zero] using h
    -- For $4$, we can find $x = 1$ that satisfies the equation.
    . use 1
      norm_num
      intro y hy₁ hy₂ h
      -- Factorize the equation.
      replace h : 2 * (y - 1) * y = 0 := by linear_combination h
      simpa [sub_eq_zero, hy₁] using h
    -- For $8$, we can find $x = -1$ that satisfies the equation.
    . use -1
      norm_num
      intro y hy₁ hy₂ h
      -- Factorize the equation.
      replace h : 2 * (y + 1) * (y - 2) = 0 := by linear_combination h
      simp [sub_eq_zero, hy₂] at h
      linear_combination h
  . -- We now prove they are the only solutions.
    rintro ⟨x, ⟨hx₁, hx₂, hx₃⟩, H⟩
    -- If $x$ is a root of the quadratic equation, then $1 - x$ is also a root by symmetry.
    specialize H (1 - x)
    -- Since the root $x$ is unique but $1 - x$ is also a root, there are only three cases left:
    -- 1. $1 - x = x$.
    -- 2. $1 - x = 0$ so it does not satisfy the condition $1 - x \neq 0$.
    -- 3. $1 - x = 2$ so it does not satisfy the condition $1 - x \neq 2$.
    simp [show 2 * (1 - x) ^ 2 - 2 * (1 - x) + 4 - a = 0 by linear_combination hx₃, imp_iff_or_not] at H
    rcases H with hx | hx | hx
    -- For all three cases, we solve for $x$ and get the value of $a$.
    . obtain rfl : x = 1 / 2 := by linarith only [hx]
      left
      linear_combination -hx₃
    . obtain rfl : x = -1 := by linarith only [hx]
      right; right
      linear_combination -hx₃
    . obtain rfl : x = 1 := by linarith only [hx]
      right; left
      linear_combination -hx₃
