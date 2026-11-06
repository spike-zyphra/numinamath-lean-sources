import Mathlib

open Real

theorem algebra_16019 :
  IsGreatest {x | ∃ θ : Fin 5 → ℝ, x = ∑ i : Fin 5, cos (θ i) * sin (θ ((i + 1) % 5))} (5 / 2) := by 
  constructor
  · -- Show 5 / 2 is in the set.
    use (fun (_ : Fin 5) => Real.pi / 4)
    have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    simp [h1, h2]
    have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    ring_nf
    <;> norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, h3]
    <;> nlinarith
  · -- Show no value greater than 5 / 2 is in the set.
    intro x hx
    rcases hx with ⟨θ, h_eq⟩
    have h1 : ∑ i : Fin 5, cos (θ i) * sin (θ ((i + 1) % 5)) ≤ 5 / 2 := by
      have eq1 : ∑ i : Fin 5, cos (θ i) * sin (θ ((i + 1) % 5)) =
        cos (θ 0) * sin (θ 1) + cos (θ 1) * sin (θ 2) + cos (θ 2) * sin (θ 3) + cos (θ 3) * sin (θ 4) + cos (θ 4) * sin (θ 0) := by 
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Fin.sum_univ_succ]
      rw [eq1]
      have h3 : cos (θ 0) * sin (θ 1) ≤ (cos (θ 0) ^ 2 + sin (θ 1) ^ 2) / 2 := by 
        linarith [sq_nonneg (cos (θ 0) - sin (θ 1) ) ]
      have h4 : cos (θ 1) * sin (θ 2) ≤ (cos (θ 1) ^ 2 + sin (θ 2) ^ 2) / 2 := by 
        linarith [sq_nonneg (cos (θ 1) - sin (θ 2) ) ]
      have h5 : cos (θ 2) * sin (θ 3) ≤ (cos (θ 2) ^ 2 + sin (θ 3) ^ 2) / 2 := by 
        linarith [sq_nonneg (cos (θ 2) - sin (θ 3) ) ]
      have h6 : cos (θ 3) * sin (θ 4) ≤ (cos (θ 3) ^ 2 + sin (θ 4) ^ 2) / 2 := by 
        linarith [sq_nonneg (cos (θ 3) - sin (θ 4) ) ]
      have h7 : cos (θ 4) * sin (θ 0) ≤ (cos (θ 4) ^ 2 + sin (θ 0) ^ 2) / 2 := by 
        linarith [sq_nonneg (cos (θ 4) - sin (θ 0) ) ]
      have h8 : cos (θ 0) * sin (θ 1) + cos (θ 1) * sin (θ 2) + cos (θ 2) * sin (θ 3) + cos (θ 3) * sin (θ 4) + cos (θ 4) * sin (θ 0) ≤ (cos (θ 0) ^ 2 + sin (θ 1) ^ 2) / 2 + (cos (θ 1) ^ 2 + sin (θ 2) ^ 2) / 2 + (cos (θ 2) ^ 2 + sin (θ 3) ^ 2) / 2 + (cos (θ 3) ^ 2 + sin (θ 4) ^ 2) / 2 + (cos (θ 4) ^ 2 + sin (θ 0) ^ 2) / 2 := by linarith [h3, h4, h5, h6, h7]
      have h9 : (cos (θ 0) ^ 2 + sin (θ 1) ^ 2) / 2 + (cos (θ 1) ^ 2 + sin (θ 2) ^ 2) / 2 + (cos (θ 2) ^ 2 + sin (θ 3) ^ 2) / 2 + (cos (θ 3) ^ 2 + sin (θ 4) ^ 2) / 2 + (cos (θ 4) ^ 2 + sin (θ 0) ^ 2) / 2 = 5 / 2 := by
        have h10 : cos (θ 0) ^ 2 + sin (θ 0) ^ 2 = 1 := by 
          exact cos_sq_add_sin_sq (θ 0)
        have h11 : cos (θ 1) ^ 2 + sin (θ 1) ^ 2 = 1 := by 
          exact cos_sq_add_sin_sq (θ 1)
        have h12 : cos (θ 2) ^ 2 + sin (θ 2) ^ 2 = 1 := by 
          exact cos_sq_add_sin_sq (θ 2)
        have h13 : cos (θ 3) ^ 2 + sin (θ 3) ^ 2 = 1 := by 
          exact cos_sq_add_sin_sq (θ 3)
        have h14 : cos (θ 4) ^ 2 + sin (θ 4) ^ 2 = 1 := by 
          exact cos_sq_add_sin_sq (θ 4)
        linarith 
      linarith 
    linarith [h_eq, h1]