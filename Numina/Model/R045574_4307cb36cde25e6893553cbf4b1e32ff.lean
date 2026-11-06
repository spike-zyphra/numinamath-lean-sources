import Mathlib

  theorem number_theory_597869 {A B : ℤ} {k : ℕ} (hA : A % 10^k = B % 10^k) (n : ℕ) :
    (A ^ n) % 10 ^ k = (B ^ n) % 10 ^ k := by
  have h2 : (A ^ n) % (10 ^ k) = (B ^ n) % (10 ^ k) := by 
    have h7 : A % (10 ^ k : ℤ) = B % (10 ^ k : ℤ) := hA
    have h8 : ∀ n : ℕ, (A ^ n) % (10 ^ k : ℤ) = (B ^ n) % (10 ^ k : ℤ) := by 
      intro n 
      have h11 : (A ^ n) % (10 ^ k : ℤ) = (B ^ n) % (10 ^ k : ℤ) := by 
        have h11 : (A ^ n) ≡ (B ^ n) [ZMOD (10 ^ k : ℤ)] := by 
          have h12 : (A : ℤ) ≡ (B) [ZMOD (10 ^ k : ℤ)] := by 
            simp [Int.ModEq, h7] 
          have h13 : (A ^ n) ≡ (B ^ n) [ZMOD (10 ^ k : ℤ)] := by 
            apply Int.ModEq.pow 
            exact h12 
          exact h13 
        simp [Int.ModEq] at h11 ⊢ 
        all_goals try tauto 
      exact h11 
    specialize h8 n 
    assumption 
  exact h2