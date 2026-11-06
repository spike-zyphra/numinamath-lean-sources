import Mathlib

theorem algebra_322005 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 4^a = 6^b) (h' : 6^b = 9^c) :
    (1 / a : ℚ) - 2 / b + 1 / c = 0 := by

  have h1 : 4^a = 9^c := by 
    linarith [h, h']

  have h2 : (2: ℕ) ^ (2*a) = (3: ℕ) ^ (2*c) := by
    have h1' : 4^a = 9^c := h1
    have h3 : (4: ℕ) ^ a = (2^2) ^ a := by ring
    have h4 : (9: ℕ) ^ c = (3^2) ^ c := by ring
    rw [h3] at h1'
    rw [h4] at h1'
    rw [← pow_mul] at h1' 
    rw [← pow_mul] at h1'
    linarith

  -- Now show a contradiction in the sidea
  -- since right side is odd and left side is even
  have h4 : (2 : ℕ) ^ (2 * a) % 2 = 0 := by
    have h10 : a > 0 := ha
    have h11 : 2 * a ≥ 2 := by omega
    have h10 : a > 0 := ha
    have h11 : 2 * a ≥ 2 := by omega
    have h12 : (2 : ℕ) ^ (2 * a) % 2 = 0 := by
      have h13 : ∀ (n : ℕ), (2 : ℕ) ^ (n + 1) % 2 = 0 := by
        intro n
        induction n with
        | zero => 
          simp
        | succ n ih =>
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.mul_mod] at ih ⊢
          <;> omega
      specialize h13 ( (2 * a) - 1 )
      have h12 : (2 * a) = ( (2 * a) - 1 ) + 1 := by omega
      rw [h12] at *
      all_goals try tauto
    exact h12

  have h5 : (3 : ℕ) ^ (2 * c) % 2 = 1 := by
    have h10 : c > 0 := hc
    have h11 : 2 * c ≥ 1 := by omega
    have h12 : (3 : ℕ) ^ (2 * c) % 2 = 1 := by
      have h13 : ∀ (n : ℕ), (3 : ℕ) ^ (n + 1) % 2 = 1 := by
        intro n
        induction n with
        | zero => 
          simp
        | succ n ih =>
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.mul_mod] at ih ⊢
          <;> omega
      specialize h13 ( (2 * c) - 1 )
      have h12 : (2 * c) = ( (2 * c) - 1 ) + 1 := by omega
      rw [h12] at *
      all_goals try tauto
    exact h12
  
  -- Now with both sides, forming equality
  have h3 : (2: ℕ) ^ (2*a) = (3: ℕ) ^ (2*c) := h2
  have h6 : (0 : ℕ) = 1 := by
    have h3' : (2 : ℕ) ^ (2 * a) = (3 : ℕ) ^ (2 * c) := h3
    have h4' : ( (2: ℕ) ^ (2 * a) ) % 2 = ( (3 : ℕ) ^ (2 * c) ) % 2 := by
      omega
    simp [h4, h5] at h4' ⊢
    <;> omega
  exfalso
  omega