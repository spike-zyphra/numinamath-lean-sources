import Mathlib
theorem algebra_21536 {O A move_north move_west move_south move_east : EuclideanSpace ℝ (Fin 2)} (a b : ℝ) (h : O = ![a, b])
    (hn: move_north = ![0,19]) (hw: move_west = ![-16,0])(hs: move_south = ![0,-3])(he: move_east = ![4,0])
    (hA : A =  O + move_north + move_west + move_south + move_east)  : dist O A = 20:= by
  rw [dist_eq_norm]
  rw [hA]
  rw [h]
  rw [hn, hw, hs, he]
  simp [norm_eq_sqrt_real_inner, inner, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring_nf
  <;> simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> norm_num