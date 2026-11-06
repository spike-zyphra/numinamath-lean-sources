import Mathlib

theorem algebra_326379 {w z : ℝ} (hw : w ≠ 0) (hz : z ≠ 0)
    (h : (1 / w + 1 / z) / (1 / w - 1 / z) = 2014) :
    (w + z) / (w - z) = -2014 := by

  have h1 : (1 / w - 1 / z) ≠ 0 := by
    by_contra h1
    rw [h1] at h
    norm_num at h

  have hwne : w ≠ z := by 
    by_contra h2
    have h4 : (1 / w - 1 / z) = 0 := by 
      rw [show z = w by linarith [h2]]
      field_simp [hw]
    contradiction

  have hwzne : w - z ≠ 0 := by 
    intro h'
    have : w = z := by linarith 
    contradiction

  have hzwne : z - w ≠ 0 := by 
    intro h'
    have : w = z := by linarith 
    contradiction
  
  have eq2 : (1 / w + 1 / z) = (2014 : ℝ) * (1 / w - 1 / z) := by 
    field_simp [h1] at h ⊢ 
    linarith 

  have eq5 : (z + w) = (2014 : ℝ) * (z - w) := by 
    have eq6 : (1 / w + 1 / z) = (z + w) / (w * z) := by 
      field_simp [hw, hz]
      <;> ring 
    have eq7 : (1 / w - 1 / z) = (z - w) / (w * z) := by 
      field_simp [hw, hz]
      <;> ring 
    rw [eq6] at eq2 
    rw [eq7] at eq2 
    have h7 : w * z ≠ 0 := by 
      apply mul_ne_zero 
      exact hw 
      exact hz 
    field_simp [h7] at eq2 
    linarith 

  have h2 : (w + z) / (w - z) = -2014 := by
    have eq8 : z + w = (2014 : ℝ) * (z - w) := eq5
    have eq9 : w - z ≠ 0 := hwzne 
    field_simp [hwzne, hzwne] 
    linarith [eq5]

  exact h2