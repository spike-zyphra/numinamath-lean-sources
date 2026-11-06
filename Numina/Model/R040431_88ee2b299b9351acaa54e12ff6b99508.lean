import Mathlib

theorem number_theory_19247 {base₉ : ℕ → ℕ} (hbase₉ : ∀n, base₉ n = Nat.ofDigits 9 (Nat.digits 10 n)): 
    base₉ 817 - base₉ 145 - base₉ 266 = base₉ 385 := by
  rw [hbase₉ 817, hbase₉ 145, hbase₉ 266, hbase₉ 385]
  norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]