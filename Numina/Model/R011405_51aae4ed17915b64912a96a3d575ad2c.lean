import Mathlib

theorem number_theory_35692 : 2005 ^ (2003 ^ 2004 + 3) ≡ 2 * 3 ^ 1 + 1 * 3 ^ 0 [MOD 9]:= by
  have h1 : 2005 ≡ 7 [MOD 9] := by norm_num [Nat.ModEq]
  have h2 : 2005 ^ (2003 ^ 2004 + 3) ≡ 7 ^ (2003 ^ 2004 + 3) [MOD 9] := by
    apply Nat.ModEq.pow 
    exact h1
  have h3 : (2003 ^ 2004 + 3) % 6 = 4 := by 
    have h4 : 2003 % 6 = 5 := by norm_num 
    have h5 : ∀ k : ℕ, (2003 ^ (2 * k) : ℕ) % 6 = 1 := by 
      intro k 
      induction k with 
      | zero =>
        norm_num 
      | succ k ih =>
        simp [pow_succ, pow_mul, Nat.mul_mod, Nat.add_mod] at ih ⊢
        all_goals try omega 
    have h6 : (2003 ^ 2004 : ℕ) % 6 = 1 := by
      specialize h5 1002 
      have h7 : 2 * 1002 = 2004 := by omega 
      rw [h7] at h5 
      omega 
    omega 
  have h8 : 7 ^ (2003 ^ 2004 + 3) ≡ 7 ^ 4 [MOD 9] := by
    have h5 : (2003 ^ 2004 + 3) % 6 = 4 := h3 
    have h6 : ∀ k : ℕ, (7 ^ (6 * k + 4) : ℕ) ≡ (7 ^ 4 : ℕ) [MOD 9] := by 
      intro k 
      induction k with 
      | zero => 
        simp [Nat.ModEq]
      | succ k ih =>
        simp [Nat.ModEq, pow_add, pow_mul, pow_succ] at ih ⊢ 
        all_goals norm_num [Nat.ModEq] at ih ⊢ 
        all_goals try omega 
    have : (2003 ^ 2004 + 3) = 6 * ( (2003 ^ 2004 + 3) / 6 ) + 4 := by 
      omega 
    rw [this] 
    exact h6 ((2003 ^ 2004 + 3) / 6) 
  have h7 : 7 ^ 4 = 2401 := by norm_num 
  have h8' : 7 ^ 4 ≡ 7 [MOD 9] := by 
    norm_num [Nat.ModEq] 
  have h9 : 2005 ^ (2003 ^ 2004 + 3) ≡ 7 [MOD 9] := by
    have h10 : 2005 ^ (2003 ^ 2004 + 3) ≡ 7 ^ (2003 ^ 2004 + 3) [MOD 9] := h2
    have h11 : 7 ^ (2003 ^ 2004 + 3) ≡ 7 ^ 4 [MOD 9] := h8 
    have h12 : 7 ^ 4 ≡ 7 [MOD 9] := h8' 
    exact Nat.ModEq.trans (Nat.ModEq.trans h10 h11) h12 
  have h10 : 2 * 3 ^ 1 + 1 * 3 ^ 0 = 7 := by norm_num 
  rw [h10] at *
  exact h9