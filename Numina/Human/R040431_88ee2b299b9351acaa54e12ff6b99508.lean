import Mathlib

/- Compute $817_9 - 145_9 - 266_9$.  Express your answer in base 9. -/
theorem number_theory_19247 {base₉ : ℕ → ℕ} (hbase₉ : ∀n, base₉ n = Nat.ofDigits 9 (Nat.digits 10 n)): 
    base₉ 817 - base₉ 145 - base₉ 266 = base₉ 385 := by 
  simp_rw [hbase₉]
  native_decide