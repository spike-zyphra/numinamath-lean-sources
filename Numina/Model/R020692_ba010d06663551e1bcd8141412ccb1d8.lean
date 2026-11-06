import Mathlib

theorem number_theory_152948 (a b : ℕ → ℤ)
    (ha : ∀ k, a k = 4^(2*k+1) + 4^(k+1) + 7)
    (hb : ∀ k, b k = 4^(2*k+1) - 4^(k+1) + 7) :
    ∀ k, 5 ∣ a k ∨ 5 ∣ b k := by 
  intro k 
  have ha1 : a k = 4 ^ (2 * k + 1) + 4 ^ (k + 1) + 7 := ha k 
  have hb1 : b k = 4 ^ (2 * k + 1) - 4 ^ (k + 1) + 7 := hb k 
  have h1 : ∀ k : ℕ, (4 : ℤ) ^ (2 * k + 1) % 5 = 4 := by 
    intro k
    induction k with 
    | zero => 
      norm_num
    | succ k ih =>
      simp [pow_succ, pow_mul, pow_add] at ih ⊢ 
      omega
  have h2 : ∀ k : ℕ, (4 : ℤ) ^ (k + 1) % 5 = if k % 2 = 0 then 4 else 1 := by 
    intro k
    induction k with
    | zero => 
      simp
    | succ k ih =>
      by_cases h : k % 2 = 0
      · -- k is even.
        simp [h, pow_succ, pow_mul] at ih ⊢
        omega
      · -- k is odd
        have : k % 2 = 1 := by
          omega
        simp [this, pow_succ, pow_mul] at ih ⊢
        omega
  by_cases h5 : k % 2 = 0 
  · -- k is even
    have h6 : k % 2 = 0 := h5 
    have h7 : (a k : ℤ) % 5 = 0 := by
      rw [ha1]
      have h8 : (4 ^ (2 * k + 1) : ℤ) % 5 = 4 := h1 k
      have h9 : (4 ^ (k + 1) : ℤ) % 5 = 4 := by
        have h10 : k % 2 = 0 := h5 
        have h11 : ( (4 : ℤ) ^ (k + 1) ) % 5 = 4 := by
          rw [h2 k]
          simp [h10]
        exact h11 
      simp [Int.add_emod, Int.mul_emod, h8, h9]
      <;> omega 
    left 
    omega
  · -- k is odd.
    have h6 : k % 2 = 1 := by 
      omega 
    have h7 : (b k : ℤ) % 5 = 0 := by 
      rw [hb1]
      have h8 : (4 ^ (2 * k + 1) : ℤ) % 5 = 4 := h1 k
      have h9 : (4 ^ (k + 1) : ℤ) % 5 = 1 := by 
        have h10 : k % 2 = 1 := h6 
        have h11 : ( (4 : ℤ) ^ (k + 1) ) % 5 = 1 := by
          rw [h2 k]
          simp [h10]
        exact h11
      simp [Int.sub_emod, Int.add_emod, Int.mul_emod, h8, h9]
      <;> omega 
    right 
    omega