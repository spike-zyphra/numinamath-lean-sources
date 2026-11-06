import Mathlib

theorem algebra_318078 (x y z : ℤ) (hx : x ∈ Finset.Icc 1 9) (hy : y ∈ Finset.Icc 1 9)
    (hz : z ∈ Finset.Icc 1 9) (hxy : x > y) (hyz : y > z) :
    3 * (x - y) = 4 * (y - z) ↔ (x, y, z) = (8, 4, 1) ∨ (x, y, z) = (9, 5, 2) := by
  simp only [Finset.mem_Icc] at hx hy hz
  constructor
  · -- Assume equality holds, prove (x,y,z) is either (8,4,1) or (9,5,2)
    intro h_eq
    -- Denote x,y,z is in 1 to 9, so finite cases
    -- First x from 1 to 9
    have h1 : x ≥ 1 := by
      omega
    have h2 : x ≤ 9 := by 
      omega
    have h3 : y ≥ 1 := by 
      omega
    have h4 : y ≤ 9 := by
      omega
    have h5 : z ≥ 1 := by 
      omega
    have h6 : z ≤ 9 := by 
      omega
    interval_cases x <;> interval_cases y <;> interval_cases z
    <;> norm_num at h_eq ⊢
    <;> try { tauto }
    <;> try { 
      omega
    }
  · -- Assume (x,y,z) is either (8,4,1) or (9,5,2), prove equality
    rintro (h | h)
    · -- First case (8,4,1)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨h8, h4, h1⟩
      rw [h8, h4, h1]
      all_goals norm_num
    · -- Second case (9,5,2)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨h9, h5, h2⟩
      rw [h9, h5, h2]
      all_goals norm_num