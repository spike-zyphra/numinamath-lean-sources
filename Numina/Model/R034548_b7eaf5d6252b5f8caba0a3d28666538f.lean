import Mathlib

open Nat

lemma lemma_1 (c y : ℕ) (hy : 0 < y) (hc : c * y % y = 0) : c * y / y = c := by
  have h1 : c * y = y * (c * y / y) + (c * y % y) := by
    rw [Nat.div_add_mod (c * y) y]
  rw [hc] at h1
  have h2 : c * y = y * (c * y / y) := by
    linarith
  have h7 : c * y = (c * y / y) * y := by
    rw [show y * (c * y / y) = (c * y / y) * y by ac_rfl] at h2
    linarith
  have h8 : c * y / y = c := by
    nlinarith [show 0 < y by linarith, show c * y = (c * y / y) * y by linarith]
  exact h8

theorem number_theory_94156 (x y u v : ℕ) (hy : 0 < y) (h : x / y = u ∧ x % y = v) :
    (x + 2 * u * y) % y = v := by
  have h1 : x / y = u := h.1
  have h2 : x % y = v := h.2
  have h3 : x = y * u + v := by
    have h4 : x = y * (x / y) + (x % y) := by
      rw [Nat.div_add_mod x y]
    rw [h1, h2] at h4
    linarith
  calc
    (x + 2 * u * y) % y
      = ( (y * u + v) + 2 * u * y ) % y := by rw [h3]
    _ = (3 * u * y + v) % y := by ring_nf
    _ = (v) % y := by 
      simp [Nat.add_mod, Nat.mul_mod]
    _ = v := by
      have h5 : v < y := by
        have h6 : x % y = v := h2
        have h7 : x % y < y := by
          apply Nat.mod_lt 
          omega
        omega
      simp [Nat.mod_eq_of_lt, h5]