import Mathlib

open Finset

theorem number_theory_84868 {f : ℕ → ℤ}
    (hf : ∀ n, f n = ∑ k ∈ Icc 1 n, Nat.totient k * (n / k) ^ 2) :
    f 2019 - f 2018 = 11431 := by 
  rw [hf, hf]
  native_decide