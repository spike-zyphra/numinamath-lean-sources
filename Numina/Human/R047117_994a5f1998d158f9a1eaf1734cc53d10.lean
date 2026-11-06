import Mathlib

/- Bobbo starts swimming at 2 feet/s across a 100 foot wide river with a current of 5 feet/s. Bobbo doesn't know that there is a waterfall 175 feet from where he entered the river. He realizes his predicament midway across the river. What is the minimum speed that Bobbo must increase to make it to the other side of the river safely?-/
theorem algebra_608380 {v_water v_peo river_dis dis v_peo': ℝ } (hv_water : v_water = 5)
  (hv_peo : v_peo = 2) (hriver : river_dis = 100) (hdis : dis = 175) (hpos : v_peo' > 0) :
  v_water * ((river_dis / 2) / v_peo) + v_water * ((river_dis / 2) / v_peo') ≤ dis → v_peo' ≥ 5 := by
  intro h
  rw [hv_water, hv_peo, hriver, hdis] at h
  have neq : v_peo' ≠ 0 := by exact Ne.symm (ne_of_lt hpos)
  field_simp at h
  norm_num at h

  have eq_aux : (500 * (2 * v_peo') + 2000) / (4 * (2 * v_peo')) = 125 + 250 / v_peo' := by
    field_simp
    ring
  rw [eq_aux] at h
  have ineq_aux : 250 / v_peo' ≤ 50 := by
    calc
      _ = 125 + 250 / v_peo' - 125 := by ring
      _ ≤  50 := by linarith
  obtain h' := (div_le_iff₀ hpos).mp ineq_aux
  rw [mul_comm] at h'
  calc 
    _ = v_peo' * 50 / 50 := by simp
    _ ≥ 250 / 50 := by linarith
    _ = 5 := by norm_num
