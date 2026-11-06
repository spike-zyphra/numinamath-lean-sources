import Mathlib

theorem algebra_19324 {f : ℕ → ℕ} (hf : ∀ n, f n = n ^ 2 + n + 17)
    (h : ∀ n ∈ Finset.Icc 0 15, Nat.Prime (f n)) :
    f 10 - f 9 = 20 := by
  have f10 : f 10 = 10 ^ 2 + 10 + 17 := hf 10
  have f9 : f 9 = 9 ^ 2 + 9 + 17 := hf 9
  calc
    f 10 - f 9 = (10 ^ 2 + 10 + 17) - (9 ^ 2 + 9 + 17) := by 
      rw [f10, f9]
    _ = 127 - 107 := by norm_num
    _ = 20 := by norm_num