import Mathlib

theorem number_theory_253873 (x : ℕ) (hx : Odd x) (hxp : x > 1) :
    ∃ y z, 0 < y ∧ 0 < z ∧ x^2 + y^2 = z^2 := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x = 2 * k + 1 := by
    omega
  have h2 : k ≥ 1 := by
    by_contra h
    push_neg at h
    have : x ≤ 1 := by
      have hk1 : k = 0 := by
        omega
      omega
    linarith
  use 2 * k ^ 2 + 2 * k
  use 2 * k ^ 2 + 2 * k + 1
  constructor
  · -- Show that 0 < y
    have h3 : k ≥ 1 := h2
    have h4 : 2 * k ^ 2 + 2 * k > 0 := by
      nlinarith [sq_nonneg (k : ℕ), sq_pos_of_pos (show k > 0 by omega)]
    linarith
  constructor
  · -- Show that 0 < z
    have h3 : k ≥ 1 := h2
    have h5 : 2 * k ^ 2 + 2 * k + 1 > 0 := by
      nlinarith [sq_nonneg (k : ℕ), sq_pos_of_pos (show k > 0 by omega)]
    linarith
  · -- Show that x^2 + y^2 = z^2
    have eq1 : x = 2 * k + 1 := h1
    have eq2 : (2 * k + 1) ^ 2 + (2 * k ^ 2 + 2 * k) ^ 2 = (2 * k ^ 2 + 2 * k + 1) ^ 2 := by
      ring_nf
    rw [eq1]
    exact_mod_cast eq2