import Mathlib

theorem number_theory_6411 {p m a : ℕ} (hp : Nat.Prime p) (hpa : p = 4 * m + 3) (ha : a ≠ 0)
    (h : (a : ZMod p) ^ ((p - 1) / 2) = 1) :
    ∃ x : ZMod p, x ^ 2 = a ∧ x = a ^ (m + 1) ∨ x = -a ^ (m + 1) := by

  have h1 : (p : ℕ) = 4 * m + 3 := hpa
  have h2 : (p - 1 : ℕ) / 2 = 2 * m + 1 := by 
    rw [h1]
    have h3 : (4 * m + 3 - 1 : ℕ) / 2 = 2 * m + 1 := by
      have h4 : 4 * m + 3 - 1 = 4 * m + 2 := by
        omega
      rw [h4]
      have h5 : (4 * m + 2 : ℕ) / 2 = 2 * m + 1 := by
        omega
      exact h5
    exact h3
  have h3 : (a : ZMod p) ^ (2 * m + 1) = 1 := by
    rw [← h2]
    exact h
  
  use a ^ (m + 1)
  left
  constructor
  · -- Show that (a^(m+1))² = a
    have h4 : ((a ^ (m + 1) : ZMod p)) ^ 2 = a := by
      have h5 : ((a ^ (m + 1) : ZMod p)) ^ 2 = (a : ZMod p) ^ (2 * m + 2) := by 
        have h6 : 2 * (m + 1) = 2 * m + 2 := by 
          omega 
        calc
          ((a ^ (m + 1) : ZMod p)) ^ 2 = (a : ZMod p) ^ (2 * (m + 1)) := by 
            rw [← pow_mul]
            <;> ring_nf 
          _ = (a : ZMod p) ^ (2 * m + 2) := by 
            rw [h6]
      rw [h5]
      have h7 : (a : ZMod p) ^ (2 * m + 2) = (a : ZMod p) := by
        calc
          (a : ZMod p) ^ (2 * m + 2) = (a : ZMod p) ^ (2 * m + 1) * (a : ZMod p) := by 
            ring_nf 
          _ = 1 * (a : ZMod p) := by 
            rw [h3] 
          _ = (a : ZMod p) := by 
            ring_nf 
      rw [h7]
    
    exact h4
  · -- Show that x = a ^ (m + 1)
    rfl