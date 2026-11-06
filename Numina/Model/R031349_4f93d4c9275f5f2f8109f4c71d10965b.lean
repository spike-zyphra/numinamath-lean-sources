import Mathlib

theorem number_theory_4283 :
    {(x, y) : ℕ × ℕ | x * 10 + y * 35 = 3545}.encard = 51 := by
  have h1 : {(x, y) : ℕ × ℕ | x * 10 + y * 35 = 3545} = Finset.filter (fun p : ℕ × ℕ => p.1 * 10 + p.2 * 35 = 3545) (Finset.Icc (0 : ℕ) 354 ×ˢ (Finset.Icc (0 : ℕ) 101)) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h2 : x ≤ 354 := by
      omega
    have h3 : y ≤ 101 := by
      omega
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide