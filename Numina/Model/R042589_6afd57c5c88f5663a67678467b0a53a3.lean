import Mathlib

theorem algebra_160797 (f : ℝ → ℝ) (r : ℝ) (hf : f = fun x => x^3 - x^2 + x + r) :
    ¬∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ f x = 0 ∧ f y = 0 ∧ f z = 0 := by

  rintro ⟨x, y, z, hx1, hy1, hz1, hfx, hfy, hfz⟩

  have eq1 : x^3 - x^2 + x + r = 0 := by
    rw [hf] at hfx
    simpa using hfx

  have eq2 : y^3 - y^2 + y + r = 0 := by
    rw [hf] at hfy
    simpa using hfy

  have eq3 : z^3 - z^2 + z + r = 0 := by
    rw [hf] at hfz
    simpa using hfz

  have eq4 : x^2 + x * y + y^2 - x - y + 1 = 0 := by
    have h1 : x^3 - x^2 + x + r = 0 := by linarith
    have h2 : y^3 - y^2 + y + r = 0 := by linarith
    have h3 : x^3 - x^2 + x + r - (y^3 - y^2 + y + r) = 0 := by linarith
    have h4 : (x - y) * (x^2 + x * y + y^2 - x - y + 1) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- x - y = 0
      exfalso
      apply hx1
      linarith
    · -- x^2 + x * y + y^2 - x - y + 1 = 0
      linarith

  -- Subtract equations to get other equations
  have eq5 : y^2 + y * z + z^2 - y - z + 1 = 0 := by
    have h2 : y^3 - y^2 + y + r = 0 := by linarith
    have h3 : z^3 - z^2 + z + r = 0 := by linarith
    have h4 : y^3 - y^2 + y + r - (z^3 - z^2 + z + r) = 0 := by linarith
    have h5 : (y - z) * (y^2 + y * z + z^2 - y - z + 1) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- y - z = 0
      exfalso
      apply hy1
      linarith
    · -- y^2 + y * z + z^2 - y - z + 1 = 0
      linarith

  -- Subtract equations to get other equations
  have eq6 : x^2 + x * z + z^2 - x - z + 1 = 0 := by
    have h1 : x^3 - x^2 + x + r = 0 := by linarith
    have h3 : z^3 - z^2 + z + r = 0 := by linarith
    have h7 : x^3 - x^2 + x + r - (z^3 - z^2 + z + r) = 0 := by linarith
    have h8 : (x - z) * (x^2 + x * z + z^2 - x - z + 1) = 0 := by
      ring_nf at h7 ⊢
      linarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- x - z = 0
      exfalso
      have hz2 : z = x := by linarith
      have hz3 : z ≠ x := hz1
      have hz4 : z = x := by linarith
      contradiction
    · -- x^2 + x * z + z^2 - x - z + 1 = 0
      linarith

  nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by
    intro h
    apply hx1
    linarith
  ), sq_pos_of_ne_zero (show (y - z) ≠ 0 by
    intro h
    apply hy1
    linarith
  ), sq_pos_of_ne_zero (show (x - z) ≠ 0 by
    intro h
    apply hz1
    linarith
  ), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)
  ]