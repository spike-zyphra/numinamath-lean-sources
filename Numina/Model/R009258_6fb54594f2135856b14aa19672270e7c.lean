import Mathlib

theorem number_theory_19209 {m : ℕ} (hm : m = 7)
  (a b : ZMod m) (ha : a = 2) (hb : b = 3) :
  ((a + b)⁻¹ : ZMod m) - (a⁻¹ + b⁻¹ : ZMod m) = 1 := by 
  rw [ha, hb, hm]
  native_decide