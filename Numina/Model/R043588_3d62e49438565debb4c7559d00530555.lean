import Mathlib

theorem number_theory_198127_1 :
    ¬∃ n ∈ Finset.Icc 10 999, Nat.ofDigits 10 (Nat.digits 10 n).reverse = 2 * n := by 
  rintro ⟨n, hn, h⟩
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨hn1, hn2⟩
  interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h ⊢
  <;> omega