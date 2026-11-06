import Mathlib

theorem number_theory_5003 (m : ℕ) (r : (ZMod m)ˣ) (hr : orderOf r = m.totient) :
    orderOf r⁻¹ = m.totient := by
  have h1 : orderOf r⁻¹ = orderOf r := by
    rw [orderOf_inv]
  rw [h1, hr]