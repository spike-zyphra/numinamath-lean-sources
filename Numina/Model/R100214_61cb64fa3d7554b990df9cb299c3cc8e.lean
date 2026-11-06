import Mathlib

theorem number_theory_8596 :
    {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 2011}.ncard = 21 := by
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 2011} = Finset.filter (fun s => (s.1 > 0 ∧ s.2.1 > 0 ∧ s.2.2 > 0 ∧ s.1^2 + s.2.1^2 + s.2.2^2 = 2011)) (Finset.Icc (0 : ℕ) 44 ×ˢ Finset.Icc (0 : ℕ) 44 ×ˢ Finset.Icc (0 : ℕ) 44) := by
    ext ⟨x, y, z⟩
    simp
    intro hx hy hz heq
    have hx' : x ≤ 44 := by nlinarith
    have hy' : y ≤ 44 := by nlinarith
    have hz' : z ≤ 44 := by nlinarith
    simp [hx', hy', hz']
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide