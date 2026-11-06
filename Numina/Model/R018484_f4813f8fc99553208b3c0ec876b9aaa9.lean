import Mathlib

theorem number_theory_197092 (a b : ℕ) (ha : 0 ≤ b ∧ b < a)
    (z : ℕ → ℕ) (hz : ∀ n, z n = a * n + b) (d : ℕ) (hd : d ≠ 0)
    (h : ∃ m, d = Nat.gcd (z m) a) :
    ∀ n, d = Nat.gcd (z n) a := by
  intro n 
  rcases h with ⟨m, hm⟩ 
  have eq1 : Nat.gcd (z n) a = Nat.gcd b a := by 
    simp only [hz]
    have : Nat.gcd (a * n + b) a = Nat.gcd b a := by 
      simp [Nat.gcd_comm, Nat.gcd_add_mul_self]
    exact this
  have eq2 : Nat.gcd (z m) a = Nat.gcd b a := by 
    simp only [hz]
    have : Nat.gcd (a * m + b) a = Nat.gcd b a := by 
      simp [Nat.gcd_comm, Nat.gcd_add_mul_self]
    exact this
  have eq3 : Nat.gcd (z n) a = Nat.gcd (z m) a := by 
    linarith [eq1, eq2]
  -- From hypothesis h: d = Nat.gcd (z m) a, and eq3: Nat.gcd (z m) a = Nat.gcd (z n) a
  have eq4 : d = Nat.gcd (z n) a := by 
    have h2 : d = Nat.gcd (z m) a := hm 
    have h3 : Nat.gcd (z m) a = Nat.gcd (z n) a := by 
      linarith [eq3]
    rw [h2, h3]
  exact eq4