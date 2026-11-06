import Mathlib

theorem number_theory_148840 {n : ℕ} (hn : 0 < n) (a : Fin n → ℤ)
    (h : ∑ i : Fin n, (-1 : ℤ)^i.1 * a i = 0) :
    ∑ i : Fin n, a i * 2^i.1 ≡ 0 [ZMOD 3] := by

  have h1 : ∀ i : Fin n, (a i * 2^i.1 : ℤ) % 3 = (a i * (-1 : ℤ) ^i.1) % 3 := by 
    intro i
    have h2 : (2^i.1 : ℤ) % 3 = ((-1 : ℤ)^i.1) % 3 := by 
      have h3 : ∀ k : ℕ, (2^k : ℤ) % 3 = ((-1 : ℤ)^k) % 3 := by
        intro k
        induction k with
        | zero => 
          simp
        | succ k ih =>
          simp [pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at ih ⊢
          omega
      specialize h3 i.1
      simpa using h3
    simp [Int.add_emod, Int.mul_emod, h2, Int.mul_emod, Int.add_emod, Int.sub_emod]
  have h2 : (∑ i : Fin n, a i * 2^i.1 : ℤ) % 3 = 
      (∑ i : Fin n, (-1 : ℤ)^i.1 * a i) % 3 := by
    have h3 : ∀ i : Fin n, (a i * 2^i.1 : ℤ) % 3 = ((-1 : ℤ)^i.1 * a i) % 3 := by
      intro i
      have h4 : (a i * 2^i.1 : ℤ) % 3 = (a i * ((-1 : ℤ)^i.1) ) % 3 := by
        apply h1 i
      have h5 : (a i * ((-1 : ℤ)^i.1) ) % 3 = ((-1 : ℤ)^i.1 * a i) % 3 := by 
        simp [Int.mul_emod, mul_comm]
      rw [h4, h5]
    simp [Finset.sum_int_mod, h3]
  
  have h3 : (∑ i : Fin n, a i * 2^i.1 : ℤ) % 3 = 0 := by
    omega

  have h4 : ∑ i : Fin n, a i * 2^i.1 ≡ 0 [ZMOD 3] := by 
    simp [Int.ModEq, h3]

  exact h4