import Mathlib

theorem algebra_12935 (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 3)
    (hzw : ‖z + w‖ = 2) : ‖1 / z + 1 / w‖ = 2 / 3 := by 
  have hz' : z ≠ 0 := by
    by_contra h
    rw [h] at hz
    simpa using hz
  have hw' : w ≠ 0 := by
    by_contra h
    rw [h] at hw
    simpa using hw
  
  have h1 : ‖1 / z + 1 / w‖ = ‖(z + w) / (z * w)‖ := by
    field_simp [hz', hw']
    <;> ring_nf <;> simp [Complex.ext_iff, mul_add, add_mul]
    <;> try tauto
  
  have h2 : ‖(z + w) / (z * w)‖ = ‖z + w‖ / ‖z * w‖ := by 
    field_simp [hz', hw']
    all_goals norm_num
    all_goals try positivity
  
  have h3 : ‖z * w‖ = ‖z‖ * ‖w‖ := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    all_goals norm_num
    all_goals try linarith [show ‖z‖ ≥ 0 by positivity, show ‖w‖ ≥ 0 by positivity]
  
  rw [h1, h2, h3, hzw, hw, hz]
  all_goals norm_num
  all_goals try positivity