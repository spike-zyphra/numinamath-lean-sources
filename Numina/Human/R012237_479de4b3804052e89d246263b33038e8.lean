import Mathlib

/- Let $G$ be a group such that $x^3 = x$ for all $x \in G$. Prove that $G$ is abelian. -/
theorem algebra_614026 {G : Type*} [grp : Group G] (h : ∀ x : G, x ^ 3 = x) :
    ∀ x y : G, x * y = y * x :=
by
  intro x y
  -- From the precondition, we have for all $x^2 = 1$, so that $x = x^{-1}$.
  have : ∀ x : G, x*x = 1 := by
    intro x
    have := h x
    apply_fun (fun y => y / x) at this
    rw [pow_three'] at this
    simp at this
    assumption
  have H : ∀ x : G, x = x⁻¹ := by
    intro x
    have : x * x * x⁻¹ = 1 * x⁻¹ := by
      rw [this]
    simp at this
    assumption
  have : 1 = x * y * x * y := by
  -- Hence that $y = x y x$
    rw [← this (x * y)]
    group
  have : y = x * y * x := by
    apply_fun (fun a => a * y⁻¹) at this
    simp at this
    rw [← H y] at this
    assumption
  -- Then we have $x y = y x$.
  apply_fun (fun a => x⁻¹ * a) at this
  conv at this =>
    rhs
    rw [←mul_assoc, ←mul_assoc]
    lhs; simp
  rw [← H x] at this
  assumption
