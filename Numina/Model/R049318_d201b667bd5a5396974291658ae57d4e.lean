import Mathlib

open Real Set
open scoped BigOperators

theorem other_160341 (a : Fin 4 → ℝ)
  (ha : ∀ i, a i ∈ Ioo 0 π) :
  ∃ v, ∀ i, ∃ t, t > 0 ∧ v * t = a i := by
    use (a 0 + a 1 + a 2 + a 3) / 4
    intro i
    have ha0 : a 0 > 0 := by 
      exact (ha 0).1
    have ha1 : a 1 > 0 := by 
      exact (ha 1).1
    have ha2 : a 2 > 0 := by 
      exact (ha 2).1
    have ha3 : a 3 > 0 := by 
      exact (ha 3).1
    have pos_v : (a 0 + a 1 + a 2 + a 3) / 4 > 0 := by
      linarith
    use (a i) / ((a 0 + a 1 + a 2 + a 3) / 4)
    constructor
    · -- Show that t is positive 
      have ha_i : a i > 0 := by
        fin_cases i <;> simp [ha0, ha1, ha2, ha3] 
      positivity
    · -- Show that v * t = a i 
      field_simp
      <;> linarith