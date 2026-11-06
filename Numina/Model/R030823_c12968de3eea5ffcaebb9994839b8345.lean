import Mathlib

theorem inequalities_220643 :
    Set.ncard {x : ℤ | abs (x^2 - 5 * x + 4) ≥ 2 ∧ abs x < 2017} = 4031 := by
  have h1 : {x : ℤ | abs (x^2 - 5 * x + 4) ≥ 2 ∧ abs x < 2017} = Finset.filter (fun x => abs (x^2 - 5 * x + 4) ≥ 2 ∧ abs x < 2017) (Finset.Icc (-2016 : ℤ) 2016) := by
    ext x
    simp 
    intro h1 h2 
    have h3 : x ≥ -2016 := by 
      rw [abs_lt] at h2 
      linarith 
    have h4 : x ≤ 2016 := by 
      rw [abs_lt] at h2 
      linarith 
    omega 
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide