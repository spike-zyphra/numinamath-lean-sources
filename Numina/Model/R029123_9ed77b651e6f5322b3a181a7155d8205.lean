import Mathlib

theorem number_theory_205424 {a b c d e : ℕ} (h : 271 ∣ Nat.ofDigits 10 [e, d, c, b, a]) :
    271 ∣ Nat.ofDigits 10 [a, e, d, c, b] := by 
  simp [Nat.ofDigits, List.foldl] at h ⊢
  omega