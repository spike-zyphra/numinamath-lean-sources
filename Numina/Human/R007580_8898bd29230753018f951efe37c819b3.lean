import Mathlib

/- Show that if \( r \) is a primitive root modulo the positive integer \( m \), then \( \bar{r} \) is also a primitive root modulo \( m \), provided that \( \bar{r} \) is the inverse of \( r \) modulo \( m \).-/
theorem number_theory_5003 (m : ℕ) (r : (ZMod m)ˣ) (hr : orderOf r = m.totient) :
    orderOf r⁻¹ = m.totient := by
  --this is exactly the proposition orderOf_inv in Mathlib
  rw [orderOf_inv]; exact hr
