import Mathlib

theorem number_theory_83679 (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k)
    (h : ∀ i j, i ≠ j → ¬(i ^ k + i ≡ j ^ k + j [MOD p])) :
    {x | ∃ i, x = (i ^ k + i) % p} = Finset.Icc 0 (p - 1) := by
  have h3 := h 0 p (by
    have hp1 : p > 0 := Nat.Prime.pos hp
    omega
  )
  have h4 : (0 ^ k + (0 : ℕ)) % p = (0 : ℕ) := by 
    have hk1 : k > 0 := by linarith
    have h2 : 0 ^ k = 0 := by
      apply zero_pow
      omega
    simp [h2]
  have h5 : (p ^ k + p) % p = (0 : ℕ) := by
    have hp1 : p > 0 := Nat.Prime.pos hp
    have hk1 : k > 0 := by linarith
    have h7 : p ^ k % p = (0 : ℕ) := by
      have hk2 : k ≥ 1 := by linarith
      have : ∀ m : ℕ, (p ^ (m + 1) : ℕ) % p = 0 := by
        intro m 
        induction m with 
        | zero =>
          simp [Nat.pow_mod, Nat.mul_mod, Nat.mod_self]
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, Nat.mod_self] at ih ⊢
          <;> try omega
      specialize this (k - 1)
      have hk1' : k - 1 + 1 = k := by omega
      rw [hk1'] at this
      exact this
    have h8 : p % p = (0 : ℕ) := by 
      simp [Nat.mod_self]
    simp [Nat.add_mod, h7, h8]
  norm_num [Nat.ModEq, h4, h5] at h3 
  all_goals
  try { 
    exfalso 
    try { 
      tauto 
    } 
    <;> try { 
      all_goals 
      try { 
        tauto 
      } 
    }
  }