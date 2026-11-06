import Mathlib

theorem algebra_191362 (f : ℝ → ℝ) (hf : f = fun x => 2*x^6 - 3*x^5 + 3*x^4 + x^3 - 3*x^2 + 3*x - 1) :
    ∑ᶠ x ∈ {x | f x = 0}, x = -1/2 := by
  have h1 : ∀ x : ℝ, f x = 2*x^6 - 3*x^5 + 3*x^4 + x^3 - 3*x^2 + 3*x - 1 := by
    intro x
    rw [hf]

  have h2 : {x : ℝ | f x = 0} = {-1, 1/2} := by
    ext x
    simp [h1]

    constructor
    · -- If $f(x) = 0$, then $x \in \{-1, \frac{1}{2}\}$.
      intro h_eq
      have h_eq1 : (x + 1) * (x - 1/2) * (x^2 - x + 1) * (2*x^2 - 2*x + 2) = 0 := by
        nlinarith [sq_nonneg (x^2 - x + 1), sq_nonneg (2 * x^2 - 2 * x + 1), sq_nonneg (x + 1), sq_nonneg (x - 1/2)]
      cases' (mul_eq_zero.mp h_eq1) with h2 h3
      · cases' (mul_eq_zero.mp h2) with h4 h5
        · cases' (mul_eq_zero.mp h4) with h6 h7
          · -- When $x + 1 = 0$, then $x = -1$.
            left
            linarith
          · -- When $x - 1/2 = 0$, then $x = 1/2$.
            right
            linarith
        · -- The quadratic $x^2 - x + 1 = 0$ has no real roots.
          nlinarith [sq_nonneg (x - 1/2)]
      · -- The quadratic $2x^2 - 2x + 2 = 0$ has no real roots.
        nlinarith [sq_nonneg (x - 1/2)]
    · -- If $x \in \{-1, \frac{1}{2}\}$, then $f(x) = 0$.
      rintro (h_eq | h_eq)
      · -- When $x = -1$.
        rw [h_eq]
        norm_num [h1]
      · -- When $x = 1/2$.
        rw [h_eq]
        norm_num [h1]

  rw [h2]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num