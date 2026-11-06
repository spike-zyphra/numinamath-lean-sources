import Mathlib

theorem algebra_219193 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (hxy : x = y + 9) (h : (10 * x + y - 3) / x = 42 ∧ (10 * x + y - 3) % x = 4) :
    x = 3443 ∧ y = 3434 := by

  have h2 := h.1
  have h3 := h.2
  have h4 : (10 * x + y - 3) = 42 * x + 4 := by
    have h1 : (10 * x + y - 3) / x = 42 := h2
    have h2 : (10 * x + y - 3) % x = 4 := h3
    have h5 : x > 0 := by
      exact hx
    have h6 : (10 * x + y - 3) = x * ((10 * x + y - 3) / x) + ((10 * x + y - 3) % x) := by
      rw [Nat.div_add_mod (10 * x + y - 3) x]
    rw [h1, h2] at h6
    nlinarith
  have h5 : y = 32 * x + 7 := by 
    omega
  have h6 : x = 3443 := by 
    nlinarith [show y > 0 by linarith, hxy]
  have h7 : y = 3434 := by 
    nlinarith [h6, hxy]
  exact ⟨h6, h7⟩