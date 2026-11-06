import Mathlib

theorem number_theory_15157 (a b : ℕ) (ha : 9 < a ∧ b < a) (hb : Nat.ofDigits a [b] = 11)
    (h : Nat.ofDigits a [3, 9, 2] + Nat.ofDigits a [8, 6, 4] = Nat.ofDigits a [b, 3, 7]) :
    a = 12 := by
  rcases ha with ⟨ha1, hab⟩
  simp [Nat.ofDigits, List.foldl] at h hb
  nlinarith [sq_pos_of_pos (show (0 : ℕ) < a by linarith), sq_nonneg (a - 12)]