import Mathlib

theorem number_theory_297937 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x - y = 58) (hxy' : (x ^ 2) % 100 = (y ^ 2) % 100) :
    x = 79 ∧ y = 21 := by
  rw [Finset.mem_Icc] at hx 
  rw [Finset.mem_Icc] at hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have hx_eq : x = y + 58 := by 
    omega
  rw [hx_eq] at hxy'
  have : y ≤ 41 := by
    omega
  interval_cases y <;> norm_num [Nat.pow_mod, hx_eq] at hxy' <;> try { 
    omega 
  }