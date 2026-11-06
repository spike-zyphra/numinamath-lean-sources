import Mathlib

theorem algebra_194788 {a m : ℕ} (ha : a ≠ 0) (hroots : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ a * p ^ 2 - m * p + 1996 = 0 ∧ a * q ^ 2 - m * q + 1996 = 0) :
    a = 2 := by
  rcases hroots with ⟨p, q, hp, hq, hneq, hp_eq, hq_eq⟩
  have h1 : a * p ^ 2 + 1996 = m * p := by 
    omega
  have h2 : a * q ^ 2 + 1996 = m * q := by 
    omega
  have h3 : a * (p ^ 2 - q ^ 2) = m * (p - q) := by 
    omega
  have h4 : p - q = 0 ∨ m * (p - q) = 0 := by 
    omega
  cases h4 with
  | inl h' =>
    -- This is addressed to the case where $p - q = 0$
    exfalso 
    have : p = q := by 
      omega 
    contradiction 
  | inr h' =>
    -- Now we can conclude that $m = 0$ or $p - q = 0$ from $m \cdot (p - q) = 0$
    have h' : p - q = 0 := by
      omega
    exfalso 
    have : p = q := by 
      omega 
    contradiction