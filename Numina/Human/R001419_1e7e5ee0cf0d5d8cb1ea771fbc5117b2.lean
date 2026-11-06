import Mathlib

/- Determine all pairs $(f, g)$ of functions from the set of real numbers to itself that satisfy  $$ g(f(x+y))=f(x)+(2 x+y) g(y) $$  for all real numbers $x$ and $y$. -/
theorem algebra_24010 :
  {(f, g) : (ℝ → ℝ) × (ℝ → ℝ) | ∀ x y, g (f (x + y)) = f x + (2 * x + y) * g y} = {(0, 0)} ∪ {((· ^ 2 + C), id) | (C : ℝ)} := by
  ext ⟨f, g⟩
  simp
  constructor
  swap
  . -- First, we examine that (0, 0) and ((· ^ 2 + C), id) are solutions.
    rintro (⟨rfl, rfl⟩ | ⟨⟨C, rfl⟩, rfl⟩)
    . simp
    . intro x y
      simp
      ring
  . intro H
    -- Next, we show that any solution must be of the form ((· ^ 2 + C), id).
    obtain ⟨A, B, rfl⟩ : ∃ A B, g = (A * · + B) := by
      -- We can show that g is linear.
      -- We swap x and y in H and subtract the original equation to get:
      -- f(x) - f(y) = (2 * y + x) * g(x) - (2 * x + y) * g(y)
      have K (x y : ℝ) : f x - f y = (2 * y + x) * g x - (2 * x + y) * g y := by
        have H1 := H x y
        have H2 := H y x
        ring_nf at H1 H2
        linear_combination H2 - H1
      -- Now we add K x 0, K 1 x, and K 0 1 and divide by 2
      -- This gives us g(x) = (g(1) - g(0)) * x + g(0)
      use g 1 - g 0, g 0
      ext x
      linear_combination (K x 0 + K 1 x + K 0 1) / 2
    simp at H
    -- We can show that f is a quadratic function.
    obtain ⟨C, rfl⟩ : ∃ C, f = fun y ↦ A * y ^ 2 - B * y + C := by
      -- Set (x, y) = (y, -y) in H
      use A * f 0 + B
      ext y
      specialize H y (-y)
      simp at H
      linear_combination -H
    -- Now set x = 0 in H
    specialize H 0
    simp at H
    -- Compare the coefficients of y^2, we get A^2 = A
    have hA : A ^ 2 = A := by linarith [H 0, H 1, H 2]
    -- This gives us that A = 0 or A = 1
    replace hA : A = 0 ∨ A = 1 := eq_zero_or_one_of_sq_eq_self hA
    rcases hA with rfl | rfl
    . -- If A = 0
      -- Now the equation becomes B = C + y * B
      -- Clearly, B = C = 0
      simp at H
      obtain rfl : B = 0 := by linarith [H 0, H 1]
      obtain rfl : C = 0 := by linarith [H 0]
      left
      simp
      rfl
    . -- If A = 1
      -- Now the equation becomes y ^ 2 - B * y + C + B = C + y * (y + B)
      -- Clearly, B = 0
      simp at H
      obtain rfl : B = 0 := by linarith [H 0, H 1]
      right
      simp
      rfl
