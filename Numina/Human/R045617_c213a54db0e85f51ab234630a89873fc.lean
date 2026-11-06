import Mathlib

/- Let $\mathbb{R}^{*}=\mathbb{R} \backslash\{0\}$ be the set of non-zero real numbers. Find all functions $f: \mathbb{R}^{*} \rightarrow \mathbb{R}^{*}$ satisfying

$$
f(x)+f(y)=f(x y f(x+y))
$$

for $x, y \in \mathbb{R}^{*}$ and $x+y \neq 0$. -/
theorem algebra_607983 (f : ℝ → ℝ) (hf : ∀ x ≠ 0, f x ≠ 0) :
    (∀ x ≠ 0, ∀ y ≠ 0, x + y ≠ 0 → f x + f y = f (x * y * f (x + y))) ↔
    (∀ x ≠ 0, f x = 1 / x) := by

    constructor
    · -- sufficiency
      rintro h
      -- by contradiction, if f x ≠ 1 / x, there exists x₀ with f x₀ ≠ 1 / x₀
      by_contra! hc
      obtain ⟨x₀, ⟨x₀nz, hx₀⟩⟩ := hc

      -- we need to apply f to two values: x = x₀ - 1 / f x₀, y = 1 / f x₀
      -- so first we show they are non-zero.
      have diff_nz : x₀ - 1 / (f x₀) ≠ 0 := by
        apply sub_ne_zero.mpr
        simp at hx₀ ⊢
        intro heq 
        have := inv_eq_iff_eq_inv.mp heq.symm 
        contradiction
      have inv_nz : 1 / (f x₀) ≠ 0 := by exact one_div_ne_zero (hf x₀ x₀nz)

      -- we have f x + f y = f (x y f (x + y)), and y * f (x + y) = 1 / f x₀ * f x₀ = 1,
      -- so we deduce f x + f y = f x
      -- the above deduction is done by simp_all
      have h_sum_f : f (x₀ - 1 / (f x₀)) + f (1 / f x₀) = f (x₀ - 1 / (f x₀)) := by simp_all

      -- from the above we have f y = f (1 / x₀) = 0, this is a contradiction
      have : f (1 / f x₀) = 0 := by linarith
      have := hf _ inv_nz
      contradiction
    · -- necessity
      rintro hf_eq x xnz y ynz h_xynz
      rw [hf_eq x xnz, hf_eq y ynz, hf_eq (x + y) h_xynz, hf_eq]
      field_simp
      ring
      simp_all
