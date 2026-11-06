import Mathlib


theorem number_theory_311434 : Nat.fib 2025 % 4 = 2 := by
  rw [show 2025 = 6 * 337 + 3 by simp]; generalize 337 = n
  suffices : ∀ n, Nat.fib (6 * n) % 4 = 0 ∧ Nat.fib (6 * n + 1) % 4 = 1 ∧
  Nat.fib (6 * n + 2) % 4 = 1 ∧ Nat.fib (6 * n + 3) % 4 = 2 ∧
  Nat.fib (6 * n + 4) % 4 = 3 ∧ Nat.fib (6 * n + 5) % 4 = 1
  · specialize this n; rcases this with ⟨_,_,_,h,_⟩
    exact h
  intro m; induction m with
  | zero => norm_num
  | succ m ihm =>
    rcases ihm with ⟨h0, h1, h2, h3, h4, h5⟩
    rw [Nat.mul_add_one]; have h6 : Nat.fib (6 * m + 6) % 4 = 0 := by
      rw [Nat.fib_add_one, show 6*m+5-1 = 6*m+4 by omega]
      rw [Nat.add_mod, h4, h5]; norm_num
    have h7 : Nat.fib (6 * m + 6 + 1) % 4 = 1 := by
      rw [Nat.fib_add_one, show 6*m+6-1 = 6*m+5 by omega]
      rw [Nat.add_mod, h6, h5]; norm_num
    have h8 : Nat.fib (6 * m + 6 + 2) % 4 = 1 := by
      rw [Nat.fib_add_one, show 6*m+7-1 = 6*m+6 by omega]
      rw [Nat.add_mod, h6, h7]; norm_num
    have h9 : Nat.fib (6 * m + 6 + 3) % 4 = 2 := by
      rw [Nat.fib_add_one, show 6*m+8-1 = 6*m+7 by omega]
      rw [Nat.add_mod, h8, h7]; norm_num
    have h10 : Nat.fib (6 * m + 6 + 4) % 4 = 3 := by
      rw [Nat.fib_add_one, show 6*m+9-1 = 6*m+8 by omega]
      rw [Nat.add_mod, h8, h9]; norm_num
    have h10 : Nat.fib (6 * m + 6 + 5) % 4 = 1 := by
      rw [Nat.fib_add_one, show 6*m+10-1 = 6*m+9 by omega]
      rw [Nat.add_mod, h10, h9]; norm_num
    split_ands; all_goals assumption