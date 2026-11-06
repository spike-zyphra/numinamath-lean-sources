import Mathlib

theorem number_theory_264160 (R : ℤ × ℤ) (hR : R = (2009, 2009)) :
    Set.ncard {p : ℤ × ℤ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < R.1 ∧ p.2 < R.2 ∧ p.2 = 3 * p.1 - 5} = 670 := by
  rw [hR]
-- The set is now { (x,y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x < 2009 ∧ y < 2009 ∧ y = 3 * x - 5 }
  have h3 : {p : ℤ × ℤ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < (2009 : ℤ) ∧ p.2 < (2009 : ℤ) ∧ p.2 = 3 * p.1 - 5} 
    = Finset.filter (fun s => (s.1 > 0 ∧ s.2 > 0 ∧ s.1 < (2009 : ℤ) ∧ s.2 < (2009 : ℤ) ∧ s.2 = 3 * s.1 - 5)) 
      (Finset.Icc (-1000 : ℤ) 3000 ×ˢ Finset.Icc (-1000 : ℤ) 3000) := by
    ext ⟨x, y⟩
    simp
    omega
  rw [h3]
  rw [Set.ncard_coe_Finset]
  native_decide