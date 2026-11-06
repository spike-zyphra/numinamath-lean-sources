import Mathlib

/- What is the shortest distance between the circles defined by $x^2-24x +y^2-32y+384=0$ and $x^2+24x +y^2+32y+384=0$? -/
theorem algebra_21057 : IsLeast {d : ℝ | ∃ C1 C2 : EuclideanSpace ℝ (Fin 2), (C1 0)^2 - 24 * (C1 0) + (C1 1)^2 - 32 * (C1 1) + 384 = 0 ∧ (C2 0)^2 + 24 * (C2 0) + (C2 1)^2 + 32 * (C2 1) + 384 = 0 ∧ d = dist C1 C2} 32 := by
  constructor
  · -- there are C1 and C2 on the respective circles such that the distance between them is 32
    use ![48 / 5, 64 / 5], ![-48 / 5, -64 / 5]
    constructor
    -- let C1 = (48/5, 64/5) and C2 = (-48/5, -64/5), then the equations of the circles are satisfied
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
    constructor
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
    -- the distance between C1 and C2 is 32
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring_nf
    have sqeq : (1024 : ℝ) = 32 ^ 2 := by
      ring
    rw [sqeq, Real.sqrt_sq]
    linarith
  · -- the distance between the two circles is greater than or equal to 32
    intro d hd
    rcases hd with ⟨C1, C2, hC1, hC2, hd⟩
    -- complete the square for the first equation
    have hC1' : ((C1 0) - 12)^2 + ((C1 1) - 16)^2 = 4^2 := by
      calc 
        _ = (C1 0)^2 - 24 * (C1 0) + (C1 1)^2 - 32 * (C1 1) + 384 + 4 ^ 2 := by
          ring
        _ = _ := by
          rw [hC1, zero_add]
    -- complete the square for the second equation
    have hC2' : ((C2 0) + 12)^2 + ((C2 1) + 16)^2 = 4^2 := by
      calc 
        _ = (C2 0)^2 + 24 * (C2 0) + (C2 1)^2 + 32 * (C2 1) + 384 + 4 ^ 2 := by
          ring
        _ = _ := by
          rw [hC2, zero_add]
    -- the centers of the circles are (12,16) and (-12,-16) respectively
    let C1' : EuclideanSpace ℝ (Fin 2) := ![12, 16]
    let C2' : EuclideanSpace ℝ (Fin 2) := ![-12, -16]
    -- the radii of the circles are equal to 4
    have hC1'_r : dist C1 C1' = 4 := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
      dsimp [C1']
      rw [hC1']
      simp only [Fin.isValue, Nat.ofNat_nonneg, Real.sqrt_sq]
    have hC2'_r : dist C2 C2' = 4 := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
      simp only [Fin.isValue, Matrix.cons_val_zero, sub_neg_eq_add, Matrix.cons_val_one, Matrix.head_cons, C2']
      rw [hC2']
      simp only [Fin.isValue, Nat.ofNat_nonneg, Real.sqrt_sq]
    -- the distance between the points (12,16) and (-12,-16) is 40
    have distr : dist C1' C2' = 40 := by
      rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
      simp only [Fin.isValue, Matrix.cons_val_zero, sub_neg_eq_add, Matrix.cons_val_one, Matrix.head_cons, C1', C2']
      have mid : ((12 + 12) ^ 2 + (16 + 16) ^ 2 : ℝ) = 40 ^ 2 := by
        ring
      rw [mid, Real.sqrt_sq]
      linarith
    -- the shortest distance between the two circles is $40 - 4 - 4 = 32$
    have h : dist C1' C2' ≤ dist C1 C1' + dist C1 C2 + dist C2 C2' := by
      have ge : dist C1' C2' ≤ dist C1' C1 + dist C1 C2' := by 
        exact dist_triangle C1' C1 C2'
      have ge2 : dist C1 C2' ≤ dist C1 C2 + dist C2 C2' := by
        exact dist_triangle C1 C2 C2'
      rw [dist_comm C1 C1']
      linarith
    rw [hC1'_r, hC2'_r] at h
    linarith


