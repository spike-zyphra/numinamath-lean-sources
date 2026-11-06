import Mathlib

theorem number_theory_323549 :
    {(n, m) : ℕ × ℕ | n * 2 + m * 3 = 2016}.encard = 337 := by
  have h1 : {(n, m) : ℕ × ℕ | n * 2 + m * 3 = 2016} = Finset.filter (fun p : ℕ × ℕ => p.1 * 2 + p.2 * 3 = 2016) (Finset.Icc (0 : ℕ) 1008 ×ˢ Finset.Icc (0 : ℕ) 672) := by
    ext ⟨n, m⟩
    simp
    intro h
    have h2 : n ≤ 1008 := by 
      omega
    have h3 : m ≤ 672 := by
      omega
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide