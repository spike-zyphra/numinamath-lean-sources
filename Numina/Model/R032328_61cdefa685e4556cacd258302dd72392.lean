import Mathlib

theorem algebra_134846 (f : ℝ → ℝ) :
    (∀ x y, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) ↔ ∀ x, f x = x * f 1 := by
  constructor
  · -- Forward direction: assuming the functional equation, proving f(x) = x*f(1)
    intro h_eq
    have h1 : f 0 = 0 := by
      specialize h_eq 0 0
      norm_num at h_eq
      linarith
    have h2 : ∀ x : ℝ, f (x ^ 2) = x * f x := by
      intro x
      specialize h_eq x 0
      simp [show f 0 = 0 by linarith] at h_eq
      linarith
    -- Show that $f(-y^2) = -y * f(y)$
    have h3 : ∀ y : ℝ, f (-y ^ 2) = -y * f y := by
      intro y
      specialize h_eq 0 y
      simp [show f 0 = 0 by linarith] at h_eq
      linarith
    have h4 : ∀ z : ℝ, f (-z) = -f z := by
      intro z
      have h5 : f z + f (-z) = 0 := by
        have eq1 := h_eq z (-z)
        have eq2 : f (z ^ 2 - (-z) ^ 2) = f 0 := by
          have : z ^ 2 - (-z) ^ 2 = 0 := by 
            ring_nf
          rw [this]
        have eq3 : (z - (-z) : ℝ) * (f z + f (-z)) = (2 * z) * (f z + f (-z)) := by
          ring
        have eq1' : f (z ^ 2 - (-z) ^ 2) = (z - (-z) : ℝ) * (f z + f (-z)) := eq1
        have eq5 : f (z ^ 2 - (-z) ^ 2) = 0 := by 
          rw [eq2, show f 0 = 0 by linarith [h1]]
        have eq6 : (2 * z) * (f z + f (-z)) = 0 := by
          linarith [eq1', eq5, eq3]
        cases' (mul_eq_zero.mp eq6) with h7 h8
        · -- Case where `2 * z = 0`, so `z = 0`
          have : z = 0 := by linarith
          rw [this] at h7 ⊢
          all_goals norm_num [h1] at *
        · -- Case where `f z + f (-z) = 0`
          linarith
      linarith
    have h5 : ∀ x y : ℝ, (x - y) * (f x + f y) = (x + y) * (f x - f y) := by
      intro x y
      have h6 := h_eq x y
      have h7 := h_eq x (-y)
      have eq1 : f (x ^ 2 - (-y) ^ 2) = f (x^2 - y^2) := by
        ring_nf
      have eq2 : (x - (-y) : ℝ) * (f x + f (-y)) = (x + y) * (f x - f y) := by
        have h7' : f (-y) = -f y := by
          apply h4 y
        rw [h7']
        all_goals ring
      have eq3 : f (x ^ 2 - (-y) ^ 2) = (x + y) * (f x - f y) := by 
        linarith [eq1, eq2, h7]
      linarith [h6, eq3]
    intro x
    have h5' := h5 x 1
    -- Solving (x -1)(f(x) + f(1)) = (x +1)(f(x) - f(1)) which simplifies to f(x) = x * f(1)
    have h11 : f x = x * f 1 := by
      nlinarith [h5']
    exact_mod_cast h11
  · -- Backward implication: if f(x) = x*f(1) then the equation holds
    intro h_eq
    intro x y
    have h1 : ∀ x : ℝ, f x = x * f 1 := by
      intro x
      specialize h_eq x
      simpa using h_eq
    have h2 : f (x ^ 2 - y ^ 2) = (x ^ 2 - y ^ 2) * f 1 := by
      have h3 : f (x ^ 2 - y ^ 2) = (x ^ 2 - y ^ 2) * f 1 := by
        specialize h1 (x ^ 2 - y ^ 2)
        linarith
      linarith
    have h3 : (x - y) * (f x + f y) = (x - y) * (x * f 1 + y * f 1) := by
      have h4 : f x = x * f 1 := by
        specialize h1 x
        linarith
      have h5 : f y = y * f 1 := by
        specialize h1 y
        linarith
      rw [h4, h5]
      <;> ring
    rw [h2]
    nlinarith [h3, sq_nonneg (x - y), sq_nonneg (x + y)]