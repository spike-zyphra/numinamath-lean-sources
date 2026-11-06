import Mathlib

theorem algebra_20971 {P : Polynomial ℂ} (hP : P.degree = 2004)
    (hP1 : P.coeff 2004 ≠ 0) (z : Fin 2004 → ℂ) (hz : ∀ i j, z i = z j → i = j)
    (hz1 : z 0 = 0) (hz2 : z 1 = 0) (hz3 : ∑ i : Fin 2004, (z i).re = ∑ i : Fin 2004, (z i).im) :
    ∑ k : Fin 2004, P.coeff k ≠ 0 := by
  have h01 : z 0 = z 1 := by 
    rw [hz1, hz2]
  have h12 : (0 : Fin 2004) = 1 := hz 0 1 h01
  simp at h12
  all_goals simpa using h12