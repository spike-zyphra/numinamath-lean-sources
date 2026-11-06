import Mathlib
open Set

/- Given positive real numbers $x, y, z$ that satisfy $x^2 - 3xy + 4y^2 - z = 0$, find the maximum value of $x + 2y - z$ when $\frac{z}{xy}$ is at its minimum. -/
theorem algebra_9046 (S : Set (ℝ × ℝ × ℝ)) (hS : S = {(x, y, z) | 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 - 3 * x * y + 4 * y^2 - z = 0}) : IsGreatest (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ x + 2 * y - z) {(x, y, z) | (x, y, z) ∈ S ∧ IsLeast (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ z / (x * y)) S) (z / (x * y))}) 2 := by
  -- We first prove that the minimum value of $\frac{z}{xy}$ is 1.
  have h : IsLeast (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ z / (x * y)) S) 1 := by
    simp [hS, IsLeast, lowerBounds]
    constructor
    -- Two goals:
    -- 1. Show that $z / (x * y) = 1$ can be achieved by some $(x, y, z) \in S$.
    -- 2. $z / (x * y) ≥ 1$ for all $(x, y, z) \in S$.
    . -- Set $(x, y, z) = (2, 1, 2)$ and simplify.
      use 2, 1, 2
      norm_num
    . -- Let $(x, y, z) \in S$ and show that $z / (x * y) ≥ 1$.
      intro a x y z hx hy hz h ha
      subst ha
      -- Rewrite the inequality as $z ≥ xy$.
      rw [one_le_div₀ (by positivity)]
      -- Substitute $z = x^2 - 3xy + 4y^2$.
      -- And the inequality is equivalent to $(x - 2y)^2 ≥ 0$.
      linarith [sq_nonneg (x - 2 * y)]

  replace h : {(x, y, z) | (x, y, z) ∈ S ∧ IsLeast (image (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ z / (x * y)) S) (z / (x * y))} = {(x, y, z) | (y > 0) ∧ (x = 2 * y) ∧ (z = 2 * y^2)} := by
    ext p
    obtain ⟨x, y, z⟩ := p
    -- Expand the definition of $S$ and simplify.
    simp [hS] at h ⊢
    -- Two implications to prove.
    constructor <;> intro k
    . -- If $(x, y, z) ∈ S$ and $z / (x * y) = 1$, then $x = 2y$ and $z = 2y^2$.
      obtain ⟨⟨hx, hy, hz, h1⟩, h2⟩ := k
      have h3 : z / (x * y) = 1 := IsLeast.unique h2 h
      field_simp at h3
      -- We have $(x - 2y)^2 = 0$.
      -- So $x = 2y$.
      replace h1 : x = 2 * y := by
        rw [← sub_eq_zero, ← sq_eq_zero_iff]
        linarith only [h1, h3]
      -- Trivial to finish.
      refine ⟨hy, ?_, ?_⟩ <;> nlinarith
    . -- If $y > 0$, $x = 2y$, and $z = 2y^2$, then $(x, y, z) ∈ S$ and $z / (x * y) = 1$.
      -- Simplifying is enough.
      obtain ⟨hy, h1, h2⟩ := k
      refine ⟨⟨by linarith, hy, by nlinarith, by nlinarith⟩, ?_⟩
      simpa [show z / (x * y) = 1 by subst x z;field_simp; ring]

  rw [h]
  clear * -
  -- Now the goal is to find the maximum value of $x + 2y - z$ when $y > 0$, $x = 2y$, and $z = 2y^2$.
  simp [IsGreatest, upperBounds]
  constructor
  -- Two goals:
  -- 1. Show that $x + 2y - z = 2$ can be achieved by some $(x, y, z)$.
  -- 2. $x + 2y - z ≤ 2$ for all $(x, y, z)$.
  . -- Set $(x, y, z) = (2, 1, 2)$ and simplify.
    use 2, 1, 2
    norm_num
  . -- $x + 2y - z = 2 - 2(y - 1)^2 ≤ 2$.
    intro a x y z hy hx hz ha
    subst x z a
    linarith [sq_nonneg (y - 1)]
