import Mathlib

open Finset

theorem number_theory_95639 {F : ℕ → ℕ} {f : ℕ → ℕ → ℕ}
    (hf : f = fun n k ↦ n % k) (hF : F = fun n ↦ sup (Icc 1 (n / 2)) (f n)) :
    (∑ n ∈ Icc 20 100, F n) % 1000 = 512 := by 
  rw [hF]
  rw [hf]
  native_decide