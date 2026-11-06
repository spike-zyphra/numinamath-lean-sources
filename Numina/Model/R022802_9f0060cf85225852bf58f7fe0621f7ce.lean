import Mathlib


theorem algebra_117268 (f : ℝ → ℝ) :
    (∀ x y, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) ↔
    ∃ k, ∀ x, f x = k * x := by
  constructor
  · -- Assume the functional equation holds, prove f is linear
    intro h
    have h1 : f 0 = 0 := by
      have h00 := h 0 0
      norm_num at h00
      linarith
    have h2 : ∀ x, f (-x) = -f x := by
      intro x
      have h_eq4 := h x (-x)
      have h_eq3 : f (x ^ 2 - (-x) ^ 2) = f 0 := by
        have h_eq4' : x ^ 2 - (-x) ^ 2 = (0 : ℝ) := by ring
        rw [h_eq4']
      rw [h1] at h_eq3
      have h_eq5 : (x - -x) * (f x + f (-x)) = 0 := by
        linarith [h_eq4, h_eq3]
      have h_eq5' : (x - -x) = 2 * x := by ring
      rw [h_eq5'] at h_eq5
      by_cases hx : x = 0
      · -- When x = 0, f(-0) = -f(0) is trivial
        rw [hx]
        norm_num
        all_goals linarith [h1]
      · -- When x ≠ 0, we can divide by 2x
        have hx2 : x ≠ 0 := hx
        have h_eq6 : f x + f (-x) = 0 := by
          apply (mul_left_inj' (show (2 * x) ≠ 0 by
            intro h'
            apply hx2
            linarith
          )).mp
          linarith
        linarith
    have h3 : ∀ x y, y * f x = x * f y := by
      intro x y
      have h_eq4 := h x y
      have h_eq5 := h x (-y)
      have h_eq6 : f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y) := h_eq4
      have h_eq7 : f (x ^ 2 - (-y) ^ 2) = (x - -y) * (f x + f (-y)) := h_eq5
      have h_eq8 : f (x ^ 2 - (-y) ^ 2) = f (x ^ 2 - y ^ 2) := by
        ring_nf
      rw [h_eq8] at h_eq7
      rw [h2 y] at h_eq7
      have h_eq9 : (x - y) * (f x + f y) = (x + y) * (f x - f y) := by
        nlinarith
      have h_eq10 : y * f x = x * f y := by
        nlinarith
      linarith
    have h4 : ∃ k, ∀ x, f x = k * x := by
      use f 1
      intro x
      have h5 := h3 x 1
      have h6 : 1 * f x = x * f 1 := by
        simpa using h5
      have h7 : f x = x * f 1 := by
        linarith
      linarith
    exact h4
  · -- Assume f is linear, prove the functional equation
    rintro ⟨k, hk⟩
    intro x y
    have h1 : f (x ^ 2 - y ^ 2) = k * (x ^ 2 - y ^ 2) := by
      specialize hk (x ^ 2 - y ^ 2)
      linarith
    have h2 : f x = k * x := by
      specialize hk x
      linarith
    have h3 : f y = k * y := by
      specialize hk y
      linarith
    calc
      f (x ^ 2 - y ^ 2) = k * (x ^ 2 - y ^ 2) := h1
      _ = (x - y) * (k * (x + y)) := by ring
      _ = (x - y) * (k * x + k * y) := by ring
      _ = (x - y) * (f x + f y) := by
        rw [h2, h3]
        all_goals nlinarith