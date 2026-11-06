import Mathlib

theorem algebra_608380 {v_water v_peo river_dis dis v_peo': ℝ } (hv_water : v_water = 5)
  (hv_peo : v_peo = 2) (hriver : river_dis = 100) (hdis : dis = 175) (hpos : v_peo' > 0) :
  v_water * ((river_dis / 2) / v_peo) + v_water * ((river_dis / 2) / v_peo') ≤ dis → v_peo' ≥ 5 := by
  intro h
  rw [hv_water, hriver, hv_peo, hdis] at h
  have h1 : (1000 * v_peo' + 2000) / (8 * v_peo') ≤ 175 := by 
    have eq1 : 5 * (( (100 : ℝ) / 2 ) / (2 : ℝ)) + 5 * (( (100 : ℝ) / 2 ) / v_peo') = (1000 * v_peo' + 2000) / (8 * v_peo') := by 
      field_simp
      <;> 
      ring
    linarith [h, eq1]

  have h2 : (1000 * v_peo' + 2000) ≤ 175 * (8 * v_peo') := by 
    have h3 : (1000 * v_peo' + 2000) / (8 * v_peo') ≤ 175 := h1 
    have h4 : (8 * v_peo') > 0 := by 
      nlinarith
    have h5 : (1000 * v_peo' + 2000) ≤ 175 * (8 * v_peo') := by 
      apply (div_le_iff₀ (by linarith)).mp at h3 
      linarith 
    linarith 
  nlinarith