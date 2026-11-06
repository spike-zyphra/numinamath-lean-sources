import Mathlib

def isPseudoprime1 (n : ℤ) (b : ℤ) : Prop := b^n.natAbs ≡ b [ZMOD n]

theorem number_theory_4821
    (n : ℤ) (n_odd : Odd n) (n_comp : ∃ m : ℕ, ∃ p : Fin m → ℤ, ∏ i, p i = n)
    : isPseudoprime1 n 1 ∧ isPseudoprime1 n (-1) := by
  constructor
  · -- Show that n is a pseudoprime to base 1
    unfold isPseudoprime1
    simp [Int.ModEq, pow_succ, pow_zero, Int.add_emod, Int.mul_emod]
  · -- Show that n is a pseudoprime to base -1
    unfold isPseudoprime1 
    have h1 : (-1 : ℤ) ^ n.natAbs = -1 := by 
      have h21 : (n : ℤ) % 2 = 1 := by 
        obtain ⟨k, hk⟩ := n_odd
        omega
      have h21a : n.natAbs % 2 = 1 := by 
        have h15 : n % 2 = 1 := by
          obtain ⟨k, hk⟩ := n_odd
          omega
        cases' abs_cases n with h h 
        · -- n ≥ 0
          omega  
        · -- n < 0
          omega
      have h33 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k + 1) = -1 := by 
        intro k
        induction k with 
        | zero => 
          norm_num
        | succ k ih => 
          simp [pow_add, pow_mul, pow_succ] at ih ⊢
          all_goals omega
      have h32 : ∃ k : ℕ, n.natAbs = 2 * k + 1 := by 
        refine' ⟨(n.natAbs - 1) / 2, by omega⟩
      rcases h32 with ⟨k, hk⟩ 
      rw [hk] 
      apply h33 k 
    rw [h1]
    all_goals simp [Int.ModEq, pow_succ, pow_zero, Int.add_emod, Int.mul_emod]