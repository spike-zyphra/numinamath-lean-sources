import Mathlib

theorem algebra_5141 :
    Set.ncard {p : ℤ × ℤ | p.2 ≤ -p.1 ^ 2 + 13 * p.1 ∧ p.2 > 0} = 364 := by 
  have h2 : {p : ℤ × ℤ | p.2 ≤ -p.1 ^ 2 + 13 * p.1 ∧ p.2 > 0} = Finset.filter (fun p : ℤ × ℤ => p.2 ≤ -p.1 ^ 2 + 13 * p.1 ∧ p.2 > 0) (Finset.Icc (1 : ℤ) 12 ×ˢ Finset.Icc (1 : ℤ) 42) := by
    ext ⟨x, y⟩
    simp 
    intro h1 h2
    have h3 : x ≥ 1 := by
      by_contra h
      push_neg at h
      have h4 : x ≤ 0 := by linarith
      nlinarith
    have h4 : x ≤ 12 := by
      by_contra h
      push_neg at h
      have h5 : x ≥ 13 := by linarith
      nlinarith
    have h5 : y ≥ 1 := by linarith
    have h6 : y ≤ 42 := by
      nlinarith [sq_nonneg (x - 7 : ℤ), sq_nonneg (x - 6 : ℤ)]
    tauto
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide