import Mathlib

theorem number_theory_104123 (x y z : ℕ) (h : 13 * x + 8 * y = 5 * z) :
    130 ∣ (x + y) * (y + z) * (z + x) := by
  have h1 : (x + y) * (y + z) * (z + x) % 2 = 0 := by
    have h2 : x % 2 = z % 2 := by
      omega
    have h3 : (z + x) % 2 = 0 := by
      omega
    simp [Nat.mul_mod, h3]
  have h2 : (x + y) * (y + z) * (z + x) % 5 = 0 := by
    have h5 : (x + y) % 5 = 0 := by
      omega
    simp [Nat.mul_mod, h5]
  have h3 : (x + y) * (y + z) * (z + x) % 13 = 0 := by
    have h13 : (y + z) % 13 = 0 := by
      omega
    simp [Nat.mul_mod, h13]
  omega