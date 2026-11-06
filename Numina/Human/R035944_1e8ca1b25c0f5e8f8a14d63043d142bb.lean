import Mathlib

/- Let $f(x)$ be a function such that $f(0) = 1$ and
\[f(xy) = f \left( \frac{x^2 + y^2}{2} \right) + (x - y)^2\]for all real numbers $x$ and $y.$  Find $f(x).$ -/
theorem algebra_12028 {f : ℝ → ℝ} (h0 : f 0 = 1) (h : ∀ x y, f (x * y) = f ((x ^ 2 + y ^ 2) / 2) + (x - y) ^ 2) :
    ∀ x, f x = 1 - 2 * x := by
  -- Specialize x = 0 at h.
  have h₁ := h 0
  simp at h₁
  rw [h0] at h₁
  -- We have f(u) = 1 - 2u for all u ≥ 0.
  replace h₁ (u : ℝ) : 0 ≤ u → f u = 1 - 2 * u := by
    intro unn
    let x : ℝ := Real.sqrt (2 * u)
    specialize h₁ x
    dsimp [x] at h₁
    rw [Real.sq_sqrt (by linarith only [unn])] at h₁
    simp at h₁
    linarith only [h₁]
  -- Now prove that the equation is true for general x.
  intro x
  specialize h x 1
  simp at h
  nth_rewrite 2 [h₁] at h
  linarith only [h]
  positivity