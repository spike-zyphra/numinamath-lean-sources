import Mathlib

theorem number_theory_5125 (p : ℕ) [inst : Fact (Nat.Prime p)] (hp : Odd p) :
    (-1 : ZMod p) ^ ((p - 1) / 2) = if p ≡ 1 [MOD 4] then 1 else -1 := by 
  have h1 : p % 2 = 1 := by
    obtain ⟨k, hk⟩ := hp
    omega
  have h2 : p % 4 = 1 ∨ p % 4 = 3 := by 
    have h1' : p % 2 = 1 := h1
    omega
  rcases h2 with (h2 | h2)
  · -- Assume p ≡ 1 [MOD 4]
    have h3 : p % 4 = 1 := h2 
    have h4 : (p - 1) / 2 % 2 = 0 := by
      omega
    have h5 : (-1 : ZMod p) ^ ((p - 1) / 2) = (1 : ZMod p) := by
      have h6 : (p - 1) / 2 % 2 = 0 := h4
      have h7 : ∃ k, (p - 1) / 2 = 2 * k := by
        refine' ⟨(p - 1) / 2 / 2, by omega⟩ 
      rcases h7 with ⟨k, hk⟩
      rw [show (p - 1) / 2 = 2 * k by omega]
      have h8 : ((-1 : ZMod p) ^ (2 * k)) = ((-1 : ZMod p) ^ 2) ^ k := by 
        rw [← pow_mul]
      have h9 : (-1 : ZMod p) ^ 2 = (1 : ZMod p) := by 
        simp [pow_two]
      rw [h8, h9]
      all_goals 
        simp
    rw [h5]
    simp [h3, Nat.ModEq]
  · -- Assume p ≡ 3 [MOD 4]
    have h3 : p % 4 = 3 := h2
    have h4 : (p - 1) / 2 % 2 = 1 := by
      omega 
    have h5 : (-1 : ZMod p) ^ ((p - 1) / 2) = (-1 : ZMod p) := by 
      have h6 : (p - 1) / 2 % 2 = 1 := h4 
      have h7 : ∃ k, (p - 1) / 2 = 2 * k + 1 := by 
        refine' ⟨(p - 1) / 2 / 2, by omega⟩
      rcases h7 with ⟨k, hk⟩ 
      rw [show (p - 1) / 2 = 2 * k + 1 by omega]
      have h8 : ((-1 : ZMod p) ^ (2 * k + 1)) = ((-1 : ZMod p) ^ (2 * k)) * ((-1 : ZMod p) ^ 1) := by 
        ring 
      rw [h8]
      have h9 : ((-1 : ZMod p) ^ (2 * k)) = (1 : ZMod p) := by
        have h10 : ((-1 : ZMod p) ^ (2 * k)) = ((-1 : ZMod p) ^ 2) ^ k := by
          rw [← pow_mul]
        have h11 : (-1 : ZMod p) ^ 2 = (1 : ZMod p) := by
          simp [pow_two]
        rw [h10, h11]
        all_goals 
          simp
      rw [h9]
      all_goals 
        simp 
    rw [h5]
    simp [h3, Nat.ModEq]