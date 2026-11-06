import Mathlib

/- Suppose that y = 3/4 x and x^y = y^x. The quantity x + y can be expressed as a rational
number r/s, where r and s are relatively prime positive integers. Find r + s. -/

theorem algebra_94497 {x y : ℝ} (hx : x > 0) (hy : y > 0)
(hxy : y = (3 / 4) * x) (h : x ^ y = y ^ x) {r s : ℕ} (hr : r > 0) (hs : s > 0)
(hcop : Nat.Coprime r s) (hxyr : x + y = r / s) : r+s = 529 := by
  -- first, a lemma so linarith works better
  have hxpx_gt_zero: x ^ x >0 := Real.rpow_pos_of_pos hx x
  -- substitute y = 3/4 x into x^y = y^x and simplify the resulting equation
  rw [hxy, Real.mul_rpow (by norm_num) (by linarith)] at h
  have h:= h.symm
  apply eq_div_of_mul_eq (by linarith) at h
  have h:((3 / 4) ^ x)^x⁻¹ = (x ^ (3 / 4 * x)/x^x)^x⁻¹ := by rw [h]
  rw [Real.rpow_mul (by linarith), ← Real.rpow_mul (by norm_num), mul_inv_cancel₀ (by linarith),
      Real.div_rpow (by rw [← Real.rpow_mul (by linarith), mul_comm, Real.rpow_mul (by linarith)]; linarith [@Real.rpow_pos_of_pos (x^x) (by linarith) (3/4:ℝ)]) (by linarith) x⁻¹,
      ← Real.rpow_mul (by linarith [Real.rpow_pos_of_pos hx (3/4)]),
      ← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith),
      mul_inv_cancel₀ (by linarith)] at h
  norm_num at h
  rw [div_eq_inv_mul _ x, ← Real.rpow_neg_one, ← Real.rpow_add (by linarith)] at h
  norm_num at h
  -- now we have 3/4 = x^(-1/4)
  have h2:=
    calc x
    _ = (x ^ (-(1:ℝ)/4)) ^ (-(4:ℝ)) := by rw [← Real.rpow_mul (by linarith)];norm_num
    _ = (3/4) ^ (-(4:ℝ)) := by ring_nf at h; rw [← h]
  norm_num at h2
  -- We've computed x, now y
  rw [h2] at hxy
  rw [hxy, h2] at hxyr
  norm_num at hxyr
  -- everything done, just need to obtain r+s
  obtain ⟨ii, jj⟩ := @Rat.div_int_inj r s 448 81 (by linarith) (by linarith) ( by simp; assumption) (by simp; norm_num) (by rify; linarith)
  norm_cast at ii jj
  rw [ii, jj]