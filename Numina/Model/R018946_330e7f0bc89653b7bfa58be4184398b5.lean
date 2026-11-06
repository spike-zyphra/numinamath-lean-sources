import Mathlib

theorem algebra_21948 : IsLeast {d : ℝ | ∃(b s e : EuclideanSpace ℝ (Fin 2)), dist b s = 10 ∧ dist b e = 8 ∧ d = dist s e} 2 := by 
  constructor
  · -- Show 2 in the set
    use ![10, 0], ![0, 0], ![2, 0]
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.vecHead, Matrix.vecTail]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf <;> norm_num
  · -- Show no less
    intro d hd
    rcases hd with ⟨b, s, e, h1, h2, h3⟩
    have h4 : dist s e ≥ 2 := by
      have h5 : dist s e + dist e b ≥ dist s b := by 
        apply dist_triangle
      have h6 : dist s b = 10 := by
        have h7 : dist s b = dist b s := by 
          simp [dist_comm]
        rw [h7, h1]
      have h7 : dist e b = 8 := by
        have h8 : dist e b = dist b e := by 
          simp [dist_comm]
        rw [h8, h2]
      rw [h7] at h5
      rw [h6] at h5
      linarith
    linarith [h3, h4]