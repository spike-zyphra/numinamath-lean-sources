import Mathlib

theorem number_theory_7305 {n : ℕ} (hn : Odd n) (h : 1 < n) (a a' : ℕ)
    (ha : Nat.Coprime a n) (ha' : Nat.Coprime a' n) (h1 : a ≡ a' [MOD n]) :
    (a : ZMod n) ^ ((n - 1) / 2) = (a' : ZMod n) ^ ((n - 1) / 2) := by
  have h2 : (a : ZMod n) = (a' : ZMod n) := by
    exact ZMod.eq_iff_modEq_nat n |>.mpr h1
  rw [h2]
  all_goals tauto