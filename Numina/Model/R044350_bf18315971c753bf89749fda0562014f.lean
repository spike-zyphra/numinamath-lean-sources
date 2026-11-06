import Mathlib

theorem number_theory_4592 (a b : ℕ) (h : 1 ≤ b) :
    ∀ k : ℕ, ∃ m : ℕ, ¬Nat.Prime (a+m*b) ∧ m > k  := by
  intro k
  use a + (b + 1) * (k + 2)
  constructor
  · -- Show that a + (a + (b + 1) * (k + 2)) * b is not prime
    have h2 : a + (a + (b + 1) * (k + 2)) * b = (a + b * (k + 2)) * (b + 1) := by
      ring_nf
      <;> omega
    rw [h2]
    have h5 : b + 1 > 1 := by
      omega
    have h6 : (a + b * (k + 2)) > 0 := by
      nlinarith [h, show k >=0 by omega, show b >=1 by omega, show a >=0 by omega]
    have h7 : (a + b * (k + 2)) > 0 := h6
    -- Apply Nat.not_prime_mul 
    apply Nat.not_prime_mul
    all_goals
      try { 
        nlinarith <;> tauto 
      }
      try { 
        omega
      }
      try { 
        nlinarith <;> omega
      }
      try { 
        nlinarith [h, show k >=0 by omega, show a >=0 by omega]
      }
  · -- Show m >k
    nlinarith [show k >=0 by omega, show a >=0 by omega, show b >=1 by omega, show (k + 2) >=2 by omega, mul_pos (show (0:ℕ) <1 by linarith) (show (0:ℕ) <1 by linarith)]
  all_goals
    try { tauto }
    try { 
      nlinarith [h, show k >=0 by omega, show a >=0 by omega]
    }
    try { nlinarith }
    try { omega }
    try { nlinarith }
    try { nlinarith [h, show k >=0 by omega, show a >=0 by omega] }