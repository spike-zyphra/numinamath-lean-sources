import Mathlib


theorem algebra_214708 (f : ℝ → ℝ) :
    (∀ x y, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) ↔
    ∃ k, ∀ x, f x = k * x := by
  constructor
  · -- Assume the functional equation holds, prove f(x) = kx.
    intro h
    have h1 : ∀ x, f (x ^ 2) = x * (f x + f 0) := by
      intro x
      specialize h x 0
      norm_num at h ⊢
      linarith
    have h2 : f 0 = 0 := by
      have eq1 := h1 0
      norm_num at eq1 ⊢
      linarith
    have h3 : ∀ x, f (x ^ 2) = x * (f x) := by
      intro x
      have eq1 := h1 x
      simp [h2] at eq1 ⊢
      linarith
    have h4 : ∀ x, f (-x) = -f x := by
      intro x
      have eq11 := h 0 x
      have eq12 := h 0 (-x)
      simp [h2] at eq11 eq12
      have eq13 : f (-x ^ 2) = -x * (f x) := by
        linarith
      have eq14 : f (-x ^ 2) = x * (f (-x)) := by
        linarith
      have eq15 : x * (f (-x) + f x) = 0 := by
        nlinarith
      by_cases hx : x = 0
      · -- x = 0, show f (-0) = -f 0
        rw [hx]
        simp [h2]
      · -- x ≠ 0, so can divide by x
        have hx' : x ≠ 0 := by
          intro h
          apply hx
          linarith
        have eq17 : f (-x) + f x = 0 := by
          apply (mul_left_inj' hx').mp
          linarith
        have eq18 : f (-x) = -f x := by linarith
        linarith
    have h6 : ∀ x y, x * f y = y * f x := by
      intro x y
      have eq1 := h x y
      have eq2 := h x (-y)
      have eq3 : f (-y) = - f y := by
        apply h4
      simp [eq3] at eq2
      nlinarith [h4 x, h4 y]
    use f 1
    intro x
    have h7 : x * f 1 = 1 * f x := by
      specialize h6 x 1
      simpa using h6
    have h8 : f x = x * (f 1) := by
      linarith
    linarith
  · -- Assume ∃k, ∀x, f x = k * x, prove the functional equation.
    rintro ⟨k, hk⟩
    intro x y
    have h1 : f (x ^ 2 - y ^ 2) = k * (x ^ 2 - y ^ 2) := by
      specialize hk (x ^ 2 - y ^ 2)
      simpa using hk
    have h2 : (x - y) * (f x + f y) = (x - y) * (k * x + k * y) := by
      have hx1 : f x = k * x := hk x
      have hy1 : f y = k * y := hk y
      rw [hx1, hy1]
    have h3 : (x - y) * (k * x + k * y) = k * (x ^ 2 - y ^ 2) := by
      ring
    have h4 : (x - y) * (f x + f y) = k * (x ^ 2 - y ^ 2) := by
      rw [h2]
      linarith
    linarith [h1, h4]