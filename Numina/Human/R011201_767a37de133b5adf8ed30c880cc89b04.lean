import Mathlib

/-Solve on ℝ:
  f(2(f(x)+f(y)))=2x+f(y)-/
theorem algebra_104907 {f : ℝ → ℝ} (h : ∀ x y, f (2 * f x + f y) = 2 * x + f y) :
    ∀ x, f x = x := by

-- we first show that f is injective --
  have h_inj : ∀ x y, f x = f y → x = y := by
    intros x y hxy
    have h1 := h x 0
    have h2 := h y 0
    -- simplify the equation --
    have h3 : 2 * x + f 0 = 2 * y + f 0 := by
      have h4 : f (2 * f x + f 0) = 2 * x + f 0 := by
        simpa using h1
      have h5 : f (2 * f y + f 0) = 2 * y + f 0 := by
        simpa using h2
      rw [show 2 * f x + f 0 = 2 * f y + f 0 by rw [hxy]] at h4
      linarith [h4, h5]
    linarith

-- then we prove that f 0 =0 --
  have h_f0 : f 0 = 0 := by
    have h_eq : ∀ y, 2 * f 0 + f y = y := by
      intro y
      have h1 := h 0 y
      have h2 : f (2 * f 0 + f y) = f y := by
        simpa using h1
      have h3 : 2 * f 0 + f y = y := by
        apply h_inj
        simpa using h2
      linarith
    have h0_eq := h_eq 0
    linarith

-- finally, we show that f x = x --
  have h_id : ∀ y, f y = y := by
    intro y
    have h_eq : 2 * f 0 + f y = y := by
      have h1 := h 0 y
      have h2 : f (2 * f 0 + f y) = f y := by
        simpa using h1
      have h3 : 2 * f 0 + f y = y := by
        apply h_inj
        simpa using h2
      linarith
    rw [h_f0] at h_eq
    linarith

  intro x
  exact h_id x
  