import Mathlib

theorem number_theory_22865 {N : ℕ} (hN6 : N = 5*6^5 + 3*6^4 + 1*6^3+3*6^2+4*6) (hN8 : N = 1*8^5+2*8^4+4*8^3+1*8^2+5*8+4) :
    N ≡ 66 [MOD 210] := by
  -- Since both expressions for N are given, but they must be consistent
  have h1 : N = 43116 := by
    norm_num [hN6]
  rw [h1]
  simp [Nat.ModEq] at *
  all_goals try { native_decide }