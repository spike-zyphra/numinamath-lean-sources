import Mathlib

/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ so that

$$
f(f(x)+x+y)=f(x+y)+y f(y)
$$

for all real numbers $x, y$. -/
theorem algebra_604186 :
  { f : ℝ → ℝ | ∀ x y : ℝ, f (f x + x + y) = f (x + y) + y * f y } = { 0 } := by
  ext f
  simp
  constructor
  -- First, we verify that f = 0 is a solution.
  swap
  {
    rintro rfl
    simp
  }
  -- Now, we show that any other solution must be 0.
  intro H
  -- It suffices to show that f(0) = 0.
  suffices h : f 0 = 0 by
    ext x
    simp
    -- Substitute (0, x) into the given functional equation.
    specialize H 0 x
    -- We get x * f(x) = 0, so either x = 0 or f(x) = 0.
    simp [h] at H
    -- Both cases imply that f(x) = 0.
    rcases H with H | H <;>
      simp [H, h]
  -- Set y = 0 in the given functional equation, and we get f(f(x) + x) = f(x).
  have H₁ x := H x 0
  simp at H₁
  -- Substitute (x, f(x)) into the given functional equation, and we get f(f(x) + x + f(x)) = f(x + f(x)) + f(x) * f(f(x)).
  have H₂ x := H x (f x)
  -- Now we do some calculations:
  have H₃ x : f x = f x + f x * f (f x) := by
    calc
      -- f(x) = f(f(x) + x) from H₁
      _ = f (f x + x) := (H₁ x).symm
      -- = f(f(f(x) + x) + (f(x) + x)) from H₁
      _ = f (f (f x + x) + (f x + x)) := (H₁ (f x + x)).symm
      -- = f(f(x) + (f(x) + x)) from H₁
      _ = f (f x + (f x + x)) := by rw [H₁ x]
      -- = f(f(x) + x + f(x)) by rearranging the terms
      _ = f (f x + x + f x) := by congr 1; ring
      -- = f(x + f(x)) + f(x) * f(f(x)) from H₂
      _ = f (x + f x) + f x * f (f x) := H₂ x
      -- = f(f(x) + x) + f(x) * f(f(x)) by rearranging the terms
      _ = f (f x + x) + f x * f (f x) := by congr 2; ring
      -- = f(x) + f(x) * f(f(x)) by H₁
      _ = f x + f x * f (f x) := by rw [H₁ x]
  -- Simplify H₃, and we get f(x) = 0 or f(f(x)) = 0.
  simp at H₃
  -- Set x = 0 in H₃, and we get f(0) = 0 or f(f(0)) = 0.
  specialize H₃ 0
  -- Set x = 0 in H₁, and we get f(f(0)) = f(0).
  specialize H₁ 0
  -- We can easily show that f(0) = 0 now.
  simp at H₁
  rw [H₁] at H₃
  simp at H₃
  exact H₃
