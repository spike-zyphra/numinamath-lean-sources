import Mathlib

theorem number_theory_309207 (a : ℕ → ℕ) (ha : a 0 = 0)
    (h : ∀ n, a (n + 1) = a n + (2 ^ n)) :
    a 2005 % 6 = 1 := by
  have eq1 : ∀ n, a n = 2 ^ n - 1 := by 
    intro n 
    induction n with 
    | zero =>
      simp [ha]
      <;> omega
    | succ n ih =>
      have eq1 : a (n + 1) = a n + (2 ^ n) := h n 
      rw [eq1, ih]
      simp [Nat.pow_succ, mul_add, mul_one, Nat.add_sub_assoc]
      <;> ring_nf
      <;> omega
  have h1 : a 2005 = 2 ^ 2005 - 1 := by 
    apply eq1 
  rw [h1]
  have h4 : (2 ^ 2005 : ℕ) % 6 = 2 := by 
    have h2 : ∀ (k : ℕ), (2 : ℕ) ^ (2 * k + 1) % 6 = 2 := by 
      intro k 
      induction k with 
      | zero => 
        norm_num 
      | succ k ih => 
        simp [pow_succ, pow_mul, mul_add] at ih ⊢ 
        <;> omega 
    have h3 : 2005 = 2 * (1002 : ℕ) + 1 := by omega 
    rw [h3]
    apply h2 1002 
  omega