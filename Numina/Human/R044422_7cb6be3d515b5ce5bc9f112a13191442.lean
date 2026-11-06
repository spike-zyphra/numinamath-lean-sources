import Mathlib

/- Let $\mathbb{R}$ be the set of all real numbers. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying for all $x, y \in \mathbb{R}$ the equation

$$
f(x)+f(y)=f(f(x) f(y)) .
$$ -/
theorem algebra_241143 :{f : ℝ → ℝ | ∀ x y, f x + f y = f (f x * f y)} = {λ _ ↦ 0} := by
  ext f
  simp
  constructor
  . intro h
    ext x₀
    -- let $c = f(x_0)$
    let c := f x₀
    have hc : f x₀ = c := rfl

    -- prove $f(c^2) = 2c$ by setting $(x_0, x_0)$
    have h1 : f (c ^ 2) = 2 * c := by
      specialize h x₀ x₀
      rw [hc, <-sq] at h
      linear_combination -h
    -- prove $f(4c^2) = 4c$ by setting $(c^2, c^2)$
    have h2 : f (4 * c ^ 2) = 4 * c := by
      specialize h (c ^ 2) (c ^ 2)
      rw [h1, <-sq, mul_pow] at h
      norm_num at h
      linear_combination -h
    -- prove $f(4c^2) = 5c$ by setting $(x_0, 4c^2)$
    have h3 : f (4 * c ^ 2) = 5 * c := by
      specialize h x₀ (4 * c ^ 2)
      rw [h2, hc, show c * (4 * c) = 4 * (c * c) by ring] at h
      rw [sq]
      linear_combination -h
    -- we have $4c = 5c$, so $c = 0$
    rw [h2] at h3
    simp at h3
    exact h3
  . intro h
    -- $f(x) = 0$ satisfies the equation
    rw [h]
    simp
