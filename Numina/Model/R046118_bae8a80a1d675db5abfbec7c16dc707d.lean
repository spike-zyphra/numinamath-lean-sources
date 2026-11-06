import Mathlib

theorem algebra_266441 (a : Fin 100 → ℤ) (h : ∑ i, (a i + 2)^2 = ∑ i, a i^2) :
    ∑ i, (a i + 4)^2 - ∑ i, a i^2 = 800 := by
  have eq2 : ∑ i, (a i + 2)^2 = ∑ i, a i^2 + 4 * (∑ i, a i) + 400 := by
    calc
      ∑ i, (a i + 2) ^ 2 = ∑ i, ((a i)^2 + 4 * (a i) + 4) := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          ring_nf
      _ = (∑ i, (a i)^2) + 4 * (∑ i, a i) + 400 := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
        all_goals ring_nf
      _ = (∑ i, a i^2) + 4 * (∑ i, a i) + 400 := by 
        simp [Finset.sum_add_distrib, Finset.mul_sum]
  -- By the condition h : ∑ i, (a i + 2)^2 = ∑ i, a i^2
  -- So from h and eq2, we can get that 4*(∑ i, a i) + 400 = 0
  have h1 : 4 * (∑ i, a i) + 400 = 0 := by
    linarith [h, eq2]
  -- solve h1, we can get that ∑ i, a i = -100
  have h2 : ∑ i, a i = -100 := by 
    linarith 
  have eq4 : ∑ i, (a i + 4)^2 = ∑ i, a i^2 + 8 * (∑ i, a i) + 1600 := by 
    calc 
      ∑ i, (a i + 4)^2 = ∑ i, ((a i)^2 + 8 * (a i) + 16) := by 
        apply Finset.sum_congr
        · rfl 
        · intro i hi
          ring_nf 
      _ = (∑ i, (a i)^2) + 8 * (∑ i, a i) + 1600 := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (∑ i, a i^2) + 8 * (∑ i, a i) + 1600 := by 
        simp [Finset.sum_add_distrib, Finset.mul_sum]
  calc 
    ∑ i, (a i + 4)^2 - ∑ i, a i^2 = (∑ i, (a i + 4)^2) - (∑ i, a i^2) := by rfl 
    _ = (∑ i, a i^2 + 8 * (∑ i, a i) + 1600) - (∑ i, a i^2) := by rw [eq4] 
    _ = 8 * (∑ i, a i) + 1600 := by 
      ring_nf 
    _ = 8 * (-100) + 1600 := by 
      rw [h2] 
    _ = 800 := by 
      norm_num