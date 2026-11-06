import Mathlib
theorem Other_24861
    (m n p a b c : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (triangle_ineq_a : b + c > a)
    (triangle_ineq_b : a + c > b)
    (triangle_ineq_c : a + b > c)
    (h_pythag_a : a^2 = n^2 + p^2)
    (h_pythag_b : b^2 = p^2 + m^2)
    (h_pythag_c : c^2 = m^2 + n^2) :
    m^2 + n^2 + p^2 ≥ 18 * (((a+b+c)/2 - a) * ((a+b+c)/2 - b) * ((a+b+c)/2 - c)) / ((a+b+c)/2) := by
  let s := (a + b + c) / 2
  let LHS := m^2 + n^2 + p^2
  let RHS := 18 * ((s - a) * (s - b) * (s - c) / s)
  have hs: s=(a + b + c) / 2 := by rfl
  have h2 : s ≠ 0 := by
    linarith
  have hem : 18 * ((s - a) * (s - b) * (s - c) / s) = 18 * (((a + b + c) / 2 - a) * ((a + b + c) / 2 - b) * ((a + b + c) / 2 - c)) / ((a + b + c) / 2) := by
    rw [hs]
    ring_nf
  rw [← show LHS= m^2 + n^2 + p^2 by rfl]
  rw [← hem]
  change LHS ≥ RHS
  have h_sum_sq_relation : LHS = (a^2 + b^2 + c^2) / 2 := by
    linarith [h_pythag_a, h_pythag_b, h_pythag_c]
  rw [h_sum_sq_relation]
  apply ge_trans
  · 
    have h_h : 3 * (a^2 + b^2 + c^2) - (a + b + c)^2 ≥ 0 := by
      calc 3 * (a^2 + b^2 + c^2) - (a + b + c)^2
        _ = 3*a^2 + 3*b^2 + 3*c^2 - (a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*c*a) := by ring
        _ = 2*a^2 + 2*b^2 + 2*c^2 - 2*a*b - 2*b*c - 2*c*a := by ring
        _ = (a - b)^2 + (b - c)^2 + (c - a)^2 := by ring
        _ ≥ 0 := by exact add_nonneg (add_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c))) (sq_nonneg (c - a))
    have h_cauchy_schwarz_type : 3 * (a^2 + b^2 + c^2) ≥ (a + b + c)^2 := by linarith
    calc (a^2 + b^2 + c^2) / 2
        _ ≥ ((a+b+c)^2 / 3) / 2 := by gcongr; linarith [h_cauchy_schwarz_type]
        _ = (2 * s)^2 / 6         := by simp [s];linarith
        _ = 4 * s^2 / 6           := by ring
        _ = 2 * s^2 / 3           := by ring
  · 
    have hs_pos : 0 < s := by dsimp [s]; linarith [ha, hb, hc]
    have h_sa_pos : 0 < s - a := by dsimp [s]; linarith [triangle_ineq_a]
    have h_sb_pos : 0 < s - b := by dsimp [s]; linarith [triangle_ineq_b]
    have h_sc_pos : 0 < s - c := by dsimp [s]; linarith [triangle_ineq_c]
    have h_amgm_base : (s-a) * (s-b) * (s-c) ≤ (((s-a) + (s-b) + (s-c)) / 3)^3 := by
      let x := s - a
      let y := s - b
      let z := s - c
      have hx_nonneg := le_of_lt h_sa_pos
      have hy_nonneg := le_of_lt h_sb_pos
      have hz_nonneg := le_of_lt h_sc_pos
      have amgm_root_pre := Real.geom_mean_le_arith_mean3_weighted (show 0 ≤ (1 : ℝ)/3 by norm_num) (show 0 ≤ (1 : ℝ)/3 by norm_num) (show 0 ≤ (1 : ℝ)/3 by norm_num) hx_nonneg hy_nonneg hz_nonneg (by norm_num)
      have amgm_root : (x * y * z)^((1 : ℝ)/3) ≤ (x + y + z) / 3 := by
        have h4 : ((s - a : ℝ) * (s - b) * (s - c)) ^ ((1 / 3 : ℝ)) = (s - a) ^ ((1 / 3 : ℝ)) * (s - b) ^ ((1 / 3 : ℝ)) * (s - c) ^ ((1 / 3 : ℝ)) := by
          rw [← Real.mul_rpow]
          rw [← Real.mul_rpow]
          all_goals
            positivity
        have h5 : ((s - a : ℝ) * (s - b) * (s - c)) ^ ((1 / 3 : ℝ)) ≤ (1 / 3 * (s - a) + 1 / 3 * (s - b) + 1 / 3 * (s - c) ) := by 
          linarith [amgm_root_pre, h4]
        have h6 : ((s - a : ℝ) * (s - b) * (s - c)) ≥ 0 := by positivity
        have h7 : (1 / 3 * (s - a) + 1 / 3 * (s - b) + 1 / 3 * (s - c) ) ≥ 0 := by
          positivity
        have h8 : (( (s - a : ℝ) * (s - b) * (s - c)) ^ ((1 / 3 : ℝ)) ) ^ 3 ≤ ( (1 / 3 * (s - a) + 1 / 3 * (s - b) + 1 / 3 * (s - c) ) ) ^ 3 := by
          apply pow_le_pow_left₀
          all_goals
            try linarith [h5, h6, h7]
            all_goals
              positivity
        have h9 : ((( (s - a : ℝ) * (s - b) * (s - c)) ^ ((1 / 3 : ℝ)) ) ^ 3 ) = ((s - a : ℝ) * (s - b) * (s - c)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals
            positivity
        rw [h9] at h8
        have h10 : (1 / 3 * (s - a : ℝ) + 1 / 3 * (s - b : ℝ) + 1 / 3 * (s - c : ℝ) ) = ( (s - a + (s - b) + (s - c)) / 3 ) := by
          ring
        rw [h10] at h8
        linarith
      rw [show s-a = x by rfl,show s-b = y by rfl,show s-c = z by rfl]
      have h2 : ((x * y * z) ^ (1 / 3 : ℝ)) ^ 3 = (x * y * z) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals positivity
      have h1 : ((x * y * z) ^ (1 / 3 : ℝ)) ^ 3 ≤ ((x + y + z) / 3) ^ 3 := by
        apply pow_le_pow_left₀
        all_goals
          try linarith
          all_goals positivity
      rw [h2] at h1
      all_goals linarith
    have h_amgm_simplified : (s-a)*(s-b)*(s-c) ≤ (s/3)^3 := by
      convert h_amgm_base using 2 
      dsimp [s]
      ring
    rw [show RHS = 18 * ((s - a) * (s - b) * (s - c) / s) by rfl]
    rw [show 18 * ((s - a) * (s - b) * (s - c) / s) = (18 * (s - a) * (s - b) * (s - c)) / s by ring]
    rw [ge_iff_le]
    calc
      18 * (s - a) * (s - b) * (s - c) / s
      _ = 18 * ((s - a) * (s - b) * (s - c)) / s := by ring
      _ ≤ 18 * ((s / 3) ^ 3 )/ s := by 
        gcongr
      _ = 2 * s ^ 2 / 3 := by
        field_simp
        ring
    