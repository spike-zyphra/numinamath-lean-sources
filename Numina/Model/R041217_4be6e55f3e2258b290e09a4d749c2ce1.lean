import Mathlib

theorem algebra_128858 (a : Fin 50 → ℝ) (h : ∑ i, (a i + 2) ^ 2 - ∑ i, a i ^ 2 = 0) :
    ∑ i, (a i + 3) ^ 2 - ∑ i, a i ^ 2 = 150 := by
  have h1 : ∑ i : Fin 50, ( (a i + 2) ^ 2 - a i ^ 2 ) = 0 := by 
    have eq1 : ∑ i : Fin 50, ( (a i + 2) ^ 2 - a i ^ 2 ) = (∑ i : Fin 50, (a i + 2) ^ 2) - (∑ i : Fin 50, a i ^ 2) := by 
      rw [Finset.sum_sub_distrib]
    rw [eq1] at *
    linarith [h]
  have h2 : ∑ i : Fin 50, ( (a i + 2) ^ 2 - a i ^ 2 ) = 4 * (∑ i : Fin 50, a i) + 200 := by
    have eq1 : ∑ i : Fin 50, ( (a i + 2) ^ 2 - a i ^ 2 ) = ∑ i : Fin 50, (4 * (a i + 1)) := by
      apply Finset.sum_congr
      · rfl 
      · intro i hi 
        simp [pow_two]
        ring
    rw [eq1]
    have eq2 : ∑ i : Fin 50, (4 * (a i + 1)) = 4 * (∑ i : Fin 50, (a i + 1)) := by 
      simp [Finset.mul_sum]
    rw [eq2]
    have eq3 : ∑ i : Fin 50, (a i + 1) = ∑ i : Fin 50, a i + 50 := by 
      simp [Finset.sum_add_distrib]
      <;> norm_num
    rw [eq3]
    all_goals ring
  have h_sum_a : ∑ i : Fin 50, a i = -50 := by
    linarith [h1, h2]
  have eq1 : ∑ i : Fin 50, (a i + 3) ^ 2 - ∑ i : Fin 50, a i ^ 2 = ∑ i : Fin 50, ((a i + 3) ^ 2 - a i ^ 2) := by 
    rw [Finset.sum_sub_distrib]
  rw [eq1]
  have h3 : ∑ i : Fin 50, ( (a i + 3) ^ 2 - a i ^ 2 ) = 6 * (∑ i : Fin 50, a i) + 450 := by 
    have eq1 : ∑ i : Fin 50, ( (a i + 3) ^ 2 - a i ^ 2 ) = ∑ i : Fin 50, (6 * (a i) + 9) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi 
        simp [pow_two]
        ring
    rw [eq1]
    have eq2 : ∑ i : Fin 50, (6 * (a i) + 9) = 6 * (∑ i : Fin 50, a i) + 450 := by 
      simp [Finset.sum_add_distrib, Finset.mul_sum]
      <;> norm_num
    rw [eq2]
  rw [h3]
  rw [h_sum_a]
  all_goals norm_num