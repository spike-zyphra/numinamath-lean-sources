import Mathlib

theorem inequalities_5238 : Set.ncard {(x, y) : ℤ × ℤ | 0 < x ∧ 0 < y ∧ 3 * x - 2 * y + 30 > 0 ∧ 3 * x + 2 * y - 78 < 0} = 385 := by
  have h1 : {(x, y) : ℤ × ℤ | 0 < x ∧ 0 < y ∧ 3 * x - 2 * y + 30 > 0 ∧ 3 * x + 2 * y - 78 < 0} = Finset.filter (fun s => 0 < s.1 ∧ 0 < s.2 ∧ 3 * s.1 - 2 * s.2 + 30 > 0 ∧ 3 * s.1 + 2 * s.2 - 78 < 0) (Finset.Icc (-20 : ℤ) 30 ×ˢ Finset.Icc (-20 : ℤ) 30) := by
    ext ⟨x, y⟩
    simp
    intro hx hy h1 h2
    have h3 : x < 27 := by omega
    have h4 : y < 39 := by omega
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide