import Mathlib

/-Find all real value functions f(x) on the reals such that f(x-y)^2 = x ^ 2 -2yf(x)+f(y)^2-/
theorem algebra_134873 : {f : ℝ → ℝ | ∀ x y, f ((x - y) ^ 2) = x ^ 2 - 2 * y * f x + f y ^ 2} =
    {f | ∀ x, f x = x} ∪ {f | ∀ x, f x = x + 1} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · -- Assume f satisfies the functional equation, we need to prove f is either the identity or f(x) = x + 1
    intro h
    -- we first derive f(0) = 0 or f(0) = 1 --
    have h00 : f 0 = 0 ∨ f 0 = 1 := by
      have h1 := h 0 0
      simp at h1
      have : f 0 * (f 0 - 1) = 0 := by linarith
      cases (mul_eq_zero.mp this) with
      | inl h0 => left; linarith
      | inr h1 => right; linarith
    cases h00 with
    | inl h0 =>
      have h_id : ∀ x, f x = x := by  -- for the case f(0) = 0, we prove f(x) = x --
        intro x
        have h1 := h x x
        simp [h0] at h1
        nlinarith [sq_nonneg (f x - x), sq_nonneg (x - f x)]
      left
      exact h_id
    | inr h0 =>
      have h1 := h 1 1     -- for the case f(0) = 1, we prove f(x) = x + 1 --
      have h2 := h 1 0
      simp [h0] at h1 h2
      have h_f1 : f 1 = 2 := by nlinarith  -- derive f(1) = 2 --
      have h_const : ∀ x, f x = x + 1 := by
        intro x
        have h3 := h x x
        simp [h0] at h3
        have h4 : (f x - (x + 1)) * (f x - (x - 1)) = 0 := by
          ring_nf at h3 ⊢   -- note that it can be factored as (f(x) - (x + 1))(f(x) - (x - 1)) = 0 --
          linarith [h3]
        cases' (mul_eq_zero.mp h4) with hfx1 hfx2
        · -- Case f(x) = x + 1
          linarith
        · -- Case f(x) = x - 1, derive contradiction using f(1) = 2
          have hfx_eq_x_minus_1 : f x = x - 1 := by linarith
          have h5 := h x 1
          have h6 := h (x - 1) 0
          simp [h0, h_f1, hfx_eq_x_minus_1] at h5 h6
          nlinarith [sq_nonneg (x - 1), sq_nonneg (f 1 - 2), h_f1, sq_nonneg (f x - (x + 1)), h6]
      right
      exact h_const
  · -- Assume f is either the identity or f(x) = x + 1, prove it satisfies the functional equation
    rintro (h | h)
    · intro x y
      simp [h]
      ring
    · intro x y
      simp [h]
      ring