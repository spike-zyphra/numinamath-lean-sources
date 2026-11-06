import Mathlib

theorem number_theory_320767 {F : ℕ → ℕ} (hF : ∀ n, F n + F (n + 1) = F (n + 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) (n : ℕ) (hn : n ≥ 2) :
    Nat.Coprime (F n) (F (n + 1)) := by 
  have h1 : ∀ (n : ℕ), Nat.Coprime (F n) (F (n + 1)) := by 
    intro n 
    induction n with 
    | zero =>
      simp [hF0, hF1]
    | succ n ih =>
      have h2 : F (n + 2) = F (n + 1) + F n := by 
        have h3 : F n + F (n + 1) = F (n + 2) := hF n 
        omega 
      have eq1 : F (n + 1 + 1) = F (n + 1) + F n := by 
        have h2' : F (n + 2) = F (n + 1) + F n := h2 
        simpa using h2' 
      rw [eq1] 
      have h3 : Nat.gcd (F (n + 1)) (F (n + 1) + F n) = Nat.gcd (F (n + 1)) (F n) := by 
        simp [Nat.gcd_add_self_right]
      have h4 : Nat.gcd (F (n + 1)) (F n) = 1 := by 
        have h5 : Nat.Coprime (F n) (F (n + 1)) := ih 
        have h6 : Nat.gcd (F n) (F (n + 1)) = 1 := by 
          rw [Nat.coprime_iff_gcd_eq_one] at h5 
          omega 
        have h7 : Nat.gcd (F (n + 1)) (F n) = Nat.gcd (F n) (F (n + 1)) := by 
          simp [Nat.gcd_comm]
        rw [h7] 
        omega 
      have h8 : Nat.gcd (F (n + 1)) (F (n + 1) + F n) = 1 := by 
        rw [h3, h4] 
      have h9 : Nat.Coprime (F (n + 1)) (F (n + 1) + F n) := by 
        rw [Nat.coprime_iff_gcd_eq_one] 
        exact h8 
      exact h9 
  specialize h1 n 
  simpa using h1