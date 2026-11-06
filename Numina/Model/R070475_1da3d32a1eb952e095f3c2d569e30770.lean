import Mathlib

theorem number_theory_11938 (x : ℤ) (hx : 4 * x ≡ 8 [ZMOD 20] ∧ 3 * x ≡ 16 [ZMOD 20]) :
    x ^ 2 ≡ 4 [ZMOD 20] := by
  rcases hx with ⟨h1, h2⟩
  norm_num [Int.ModEq] at h1 h2 ⊢
  have h3 : x % 20 = 12 := by 
    omega
  simp [h3, pow_two, Int.mul_emod, Int.add_emod, Int.sub_emod]
  <;> omega