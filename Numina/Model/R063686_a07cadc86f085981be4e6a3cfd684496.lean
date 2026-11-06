import Mathlib

theorem algebra_203814 {x y z : ℤ} (hx : x + 47 = 547) (hy : y - 60 = 380) (hz : 570 + z = 710) :
    x = 500 ∧ y = 440 ∧ z = 140 := by
  have hx' : x = 500 := by
    linarith
  have hy' : y = 440 := by
    linarith
  have hz' : z = 140 := by
    linarith
  exact ⟨hx', hy', hz'⟩