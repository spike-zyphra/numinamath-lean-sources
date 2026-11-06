import Mathlib

theorem algebra_266317 : Set.ncard {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 3 * x + y = 100} = 33 := by
  have : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 3 * x + y = 100} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ 3 * p.1 + p.2 = 100) (Finset.Icc (0 : ℕ) 33 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨x, y⟩
    simp 
    intro h1 h2 h3
    have h4 : x ≤ 33 := by 
      omega 
    have h5 : y ≤ 100 := by 
      omega 
    omega 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide