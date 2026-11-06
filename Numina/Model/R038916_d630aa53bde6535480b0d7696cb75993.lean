import Mathlib

open Real

theorem algebra_324637 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (f : ℝ → ℝ)
    (hf : f = fun x => a ^ x) (g : ℝ → ℝ) (hg : g = fun x => logb a x)
    (A B C D : ℝ) (hA : f A = 9 - A) (hB : g B = 9 - B)
    (hC : f C = 0) (hD : g D = 0) (htrisect : B = (A + C) / 3 ∧ D = (B + C) / 3) :
    a = 6 ^ ((1 : ℝ) / 3) ∨ a = 3 ^ ((1 : ℝ) / 6) := by

  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have h1 : f C = 0 := hC
  rw [hf] at h1
  simp at h1
  have h2 : a ^ C > 0 := by
    apply Real.rpow_pos_of_pos
    linarith
  linarith