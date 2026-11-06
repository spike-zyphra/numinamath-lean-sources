import Mathlib

open Real
open scoped BigOperators

theorem number_theory_7294 {p a1 a2 : ℕ} (hp : Nat.Prime p) (h1 : 3 ≤ p) (h2 : a1 ≡ a2 [MOD p]) :
  (a1 : ZMod p) ^ ((p-1)/2) = (a2 : ZMod p) ^ ((p-1)/2) := by 
  have h3 : (a1 : ZMod p) = (a2 : ZMod p) := by 
    exact ZMod.eq_iff_modEq_nat p |>.mpr h2
  rw [h3]