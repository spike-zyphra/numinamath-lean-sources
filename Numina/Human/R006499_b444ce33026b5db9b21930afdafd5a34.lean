import Mathlib

theorem number_theory_637789 {s : ℕ} (hs : 3 ≤ s) (M : ℕ) (hM : M = 10 ^ s) (n : ℤ)
  (hn : M / 10 ≤ n ∧ n < M) (k: ℤ) (hk : 7 * n = M * k + 638) 
  (inv7 : ZMod M) (hinv : (7 * inv7) = 1) :
  n = (inv7 * 638) := by 
  have h1 : (n : ZMod M) = (n : ZMod M) * 1 := by 
    simp
  rw [h1, ←hinv, ←mul_assoc]
  have h2 : ((M : ℤ) * k + 638 : ZMod M) = 638 := by 
    refine add_eq_of_eq_sub ?_
    simp
  have h3 : ((7 * n : ℤ) : ZMod M) = ↑M * k + 638 := by 
    simp [hk]
  simp at h3
  have h4 : ↑n * 7 * inv7 = inv7 * (7 * n) := by 
    ring
  rw [h4,  h3]