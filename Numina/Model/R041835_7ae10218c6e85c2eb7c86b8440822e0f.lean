import Mathlib

theorem number_theory_22824 (k : ℕ) (h : k + 200 ≡ 3 [MOD 7]) :
    k ≡ 6 [MOD 7] := by 
  have h1 : (k + 200) % 7 = 3 := h
  simp [Nat.ModEq] at h ⊢
  omega