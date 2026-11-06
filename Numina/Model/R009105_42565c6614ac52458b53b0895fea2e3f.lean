import Mathlib

open Classical

theorem amc_algebra_1183 (njr nsr tot_jr tot_sr : ℚ) (hgt : njr > 0) (hjs : nsr = 9 * njr) (havg : (tot_jr + tot_sr) / (njr + nsr) = 84) (hsr_avg : tot_sr / nsr = 83) : (tot_jr / njr = 93) := by
  have h1 : tot_jr + tot_sr = 84 * (njr + nsr) := by
    have h1 : njr + nsr ≠ 0 := by
      nlinarith
    field_simp at havg ⊢
    linarith
  
  have h2 : tot_sr = 83 * nsr := by 
    have h2 : nsr ≠ 0 := by
      nlinarith [hgt, hjs]
    field_simp at hsr_avg ⊢
    linarith
  
  have h3 : nsr = 9 * njr := hjs
  
  rw [h2, h3] at h1
  
  have h4 : tot_jr = 93 * njr := by
    nlinarith
  
  have h5 : njr ≠ 0 := by
    nlinarith
  
  have h6 : tot_jr / njr = 93 := by
    rw [h4]
    field_simp at *
    <;> nlinarith
  
  exact h6