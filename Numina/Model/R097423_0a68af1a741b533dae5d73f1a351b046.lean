import Mathlib

theorem algebra_16702 {a b : ℤ} (ha : 4 ∣ a) (hb : 8 ∣ b) :
    2 ∣ a + b ∧ 4 ∣ a + b := by
  constructor
  · -- Show that 2 divides a + b.
    have ha2 : 2 ∣ a := by
      omega
    have hb2 : 2 ∣ b := by
      omega
    omega
  · -- Show that 4 divides a + b.
    have hb4 : 4 ∣ b := by
      omega
    omega