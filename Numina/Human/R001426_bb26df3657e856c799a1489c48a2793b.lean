import Mathlib

/- 1. (AUS 6) Let $f$ be a function that satisfies the following conditions: (i) If $x>y$ and $f(y)-y \geq v \geq f(x)-x$, then $f(z)=v+z$, for some number $z$ between $x$ and $y$. (ii) The equation $f(x)=0$ has at least one solution, and among the solutions of this equation, there is one that is not smaller than all the other solutions; (iii) $f(0)=1$. (iv) $f(1987) \leq 1988$. (v) $f(x) f(y)=f(x f(y)+y f(x)-x y)$.  Find $f(1987)$. -/
theorem algebra_24054 {f : ℝ → ℝ}
    (h1 : ∀ x y v, x > y → f y - y ≥ v ∧ v ≥ f x - x → ∃ z, x < z ∧ z < y ∧ f z = v + z)
    (h2 : ∃ x, f x = 0 ∧ ∀ y, f y = 0 → y ≤ x)
    (h3 : f 0 = 1)
    (h4 : f 1987 ≤ 1988)
    (h5 : ∀ x y, f x * f y = f (x * f y + y * f x - x * y)) :
    f 1987 = 1988 := by 
  obtain ⟨x₀, hx, hy⟩ := h2
  -- ∀ x, f (x₀ * (f x - x)) = 0
  have eq1 : ∀ x, f (x₀ * (f x - x)) = 0 := by 
    intro x
    calc 
      _ = f (x * f x₀ + x₀ * f x - x₀ * x) := by 
        rw [hx]
        simp
        congr
        ring
      _ = f x * f x₀ := by 
        rw [h5]
        ring_nf
      _ = 0 := by 
        rw [hx]
        simp
  -- then deduces from the above property h2, then we have x₀ ≥ x₀ * (f x - x) 
  have ineq1 : ∀ x,  x₀ ≥ x₀ * (f x - x)  := by
    intro x
    apply hy
    exact eq1 x
  have xneg : x₀ < 0 := by 
    -- suppose x₀ > 0
    by_cases xpos : x₀ > 0 
    · 
      obtain aux := h1 x₀ 0 0 xpos 
      have aux1 : f 0 - 0 ≥ 0 ∧ 0 ≥ f x₀ - x₀ := by 
        constructor
        rw [h3]
        linarith
        rw [hx]
        linarith
      obtain aux2 := aux aux1
      obtain ⟨z, hz1, hz2, hz3⟩ := aux2
      simp at hz3
      obtain eq2 := eq1 z
      rw [hz3] at eq2
      simp at eq2
      rw [h3] at eq2
      linarith
    -- suppose x₀ = 0
    by_cases hx0 : x₀ = 0
    · rw [hx0, h3] at hx
      linarith
    -- then deduce that x₀ = 0
    simp at xpos
    exact lt_of_le_of_ne xpos hx0
  have xneq : x₀ ≠ 0 := by 
    linarith
  have ineq2 : ∀ (x : ℝ), (f x - x) ≥ 1 := by 
    intro x
    calc 
      _ = (x₀ * (f x - x)) / x₀ := by 
        field_simp
      _ ≥ x₀ / x₀ := by
        exact (div_le_div_right_of_neg xneg).mpr (hy (x₀ * (f x - x)) (eq1 x))
      _ = 1 := by 
        field_simp
  obtain ineq3 := ineq2 1987
  linarith