import Mathlib

  theorem number_theory_36470 {a b : ℕ} (ha : a < 10) (hb : b < 10)(h : Nat.factorial 34 = 2952327990390041408476186096435 * 10^8 + 10^26 * a + 10^7 * b) :
    a = 6 ∧ b = 2 := by
  norm_num [Nat.factorial] at h ⊢
  omega