import Mathlib

def f' : ℕ → ℕ
| 0 => 1
| n + 1 => if Even n then (f' n) + 1 else (f' n) * 2

theorem algebra_20871 : f' 99 = 3 * 2 ^ k - 1 ↔ k = 49 := by
  constructor
  · -- Assume f' 99 = 3 * 2 ^ k - 1, prove k = 49
    intro h
    have eq : f' 99 = 3 * 2 ^ 49 - 1 := by 
      native_decide
    rw [eq] at h
    have eq2 : 3 * 2 ^ 49 - 1 = 3 * 2 ^ k - 1 := by
      omega
    have h1 : 3 * 2 ^ 49 = 3 * 2 ^ k := by
      omega
    have h2 : 2 ^ 49 = 2 ^ k := by
      omega
    have h3 : 49 = k := by
      exact Nat.pow_right_injective (by norm_num) h2
    omega
  · -- Assume k = 49, prove f' 99 = 3 * 2 ^ k - 1
    intro hk
    rw [hk]
    have eq : f' 99 = 3 * 2 ^ 49 - 1 := by 
      native_decide
    omega