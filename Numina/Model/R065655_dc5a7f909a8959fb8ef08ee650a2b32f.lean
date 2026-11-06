import Mathlib

open Nat

theorem number_theory_3954 : {n : ℕ | 2 ≤ n ∧ n ≤ 1024 ∧ 2^(n - 2) ∣ n !}.encard = 55 := by
  have h1 : {n : ℕ | 2 ≤ n ∧ n ≤ 1024 ∧ 2^(n - 2) ∣ n !} = Finset.filter (fun n => 2^(n - 2) ∣ n !) (Finset.Icc (2 : ℕ) 1024) := by
    ext n
    simp
    tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide