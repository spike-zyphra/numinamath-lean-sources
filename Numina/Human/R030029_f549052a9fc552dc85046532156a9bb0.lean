import Mathlib

/- Find all functions $f(x)$ that are defined for all $x$ and satisfy the relation

$$
x f(y)+y f(x)=(x+y) f(x) f(y)
$$

for all $x, y$. -/
theorem algebra_231488 :
  {f : ℝ → ℝ | ∀ x y : ℝ, x * (f y) + y * (f x) = (x + y) * (f x) * (f y)} =
  {f : ℝ → ℝ | (∀ x : ℝ, f x = 0) ∨ 
               (∃ c : ℝ, f 0 = c ∧ ∀ x : ℝ, x ≠ 0 → f x = 1)} := by
  apply Set.ext
  intro f
  simp
  constructor
  intro hfxy
  -- Let $x=y$. Then we get $2 x f(x)=2 x(f(x))^{2}$. If $x \neq 0$, then $f(x)=0$ or 1.
  have h1 : ∀ x ≠ 0 , f x = 0 ∨ f x = 1 := by
    intro x hx
    specialize hfxy x x
    rw [← two_mul,← two_mul,← mul_assoc] at hfxy
    simp [hx] at hfxy
    exact id (Or.symm hfxy)
  -- Suppose that $f(a)=0$ for some $a \neq 0$. Setting $x=a$, we get $a f(y)=0$ for all $y$, i.e., $f=0$.
  by_cases h2 : ∃ x ≠ 0, f x = 0
  · rcases  h2 with ⟨x,hx1,hx2⟩
    left
    intro y
    specialize hfxy x y
    simp [hx1,hx2] at hfxy
    exact hfxy
  -- Suppose that $f(a)=1$ for some $a \neq 0$. Setting $x=a$, we get $a f(y)+y=(a+y) f(y)$, i.e., $y=y f(y)$. Thus, $f(y)=1$ for all $y \neq 0$.
  right
  intro x hx
  simp at h2
  specialize h2 x hx
  specialize h1 x hx
  simp [h2] at h1
  exact h1
  -- As a result, we obtain that either $f(x)=0$ for all $x$, or $f(x)=1$ for all $x \neq 0$ and $f(0)=c-$ an arbitrary number.
  intro hf
  rcases hf with hf |hf
  intro x y 
  rw [hf x,hf y] ;simp
  intro x y
  by_cases hx : x = 0
  <;> by_cases hy : y = 0
  <;> simp [hf,hx,hy]