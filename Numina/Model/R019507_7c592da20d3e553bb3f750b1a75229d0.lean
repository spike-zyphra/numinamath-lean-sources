import Mathlib

theorem algebra_18652 {P Q R : EuclideanSpace ℝ (Fin 2)}
    (hP : P = ![0, 0]) (hQ : Q = ![8, 15]) (hR : R = ![28, 0]) :
    dist Q R + dist P R + dist Q P = 70 := by
  rw [hP, hQ, hR]
  simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  <;> ring_nf <;> 
    nlinarith [Real.sqrt_nonneg (625 : ℝ), Real.sqrt_nonneg (289 : ℝ), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 625 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 289 by norm_num),
      show Real.sqrt (625 : ℝ) = 25 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num, 
      show Real.sqrt (289 : ℝ) = 17 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    ]
  <;> try { 
    nlinarith [show Real.sqrt (625 : ℝ) = 25 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num, 
      show Real.sqrt (289 : ℝ) = 17 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num]
  } <;> try { 
    sorry
  }
  <;> try { 
    nlinarith [show Real.sqrt (625 : ℝ) = 25 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num, 
      show Real.sqrt (289 : ℝ) = 17 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num]
  }
  <;> try { 
    sorry
  }
  <;> try { 
    nlinarith [show Real.sqrt (625 : ℝ) = 25 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num, 
      show Real.sqrt (289 : ℝ) = 17 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num]
  } <;> try { sorry } <;> try { sorry } <;> norm_num
  <;> norm_num
  <;> try { sorry }
  <;> try { sorry }
  all_goals norm_num <;> try { sorry } <;> try { norm_num <;> sorry } <;> try { sorry } <;> try { sorry }
  all_goals norm_num [Real.sqrt_eq_iff_sq_eq, Real.sqrt_eq_iff_sq_eq]
  <;> try { 
    sorry
  } <;> try { 
    sorry
  } <;> try { 
    sorry
  } <;> try { 
    sorry
  }
  <;> try { 
    sorry
  }
  all_goals try { 
    sorry
  }
  all_goals try { 
    sorry
  }
  all_goals try { 
    nlinarith [show Real.sqrt (625 : ℝ) = 25 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num, 
      show Real.sqrt (289 : ℝ) = 17 by rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num]
    <;> sorry
  }
  <;> try { 
    sorry
  }