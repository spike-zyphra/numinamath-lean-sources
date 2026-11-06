import Mathlib

theorem algebra_241427 {z : ℂ} (hz : Complex.abs (z + 1) = 1 ∧ Complex.abs (z ^ 2 + 1) = 1) :
    z = 0 ∨ z = (-1 - Real.sqrt 3 * Complex.I) / 2 ∨ z = (-1 + Real.sqrt 3 * Complex.I) / 2 := by 
  rcases hz with ⟨h1, h2⟩
  have eq1 : Complex.abs (z + 1) = Real.sqrt ((z.re + 1) ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Complex.I_sq]
    <;> ring
  have eq2 : Complex.abs (z ^ 2 + 1) = Real.sqrt ((z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Complex.I_sq]
    <;> ring
  rw [eq1] at h1
  rw [eq2] at h2
  have eq3 : (z.re + 1) ^ 2 + z.im ^ 2 = 1 := by
    calc
      (z.re + 1) ^ 2 + z.im ^ 2 = (Real.sqrt ((z.re + 1) ^ 2 + z.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1 ^ 2 := by rw [h1]
      _ = (1 : ℝ) := by norm_num
  have eq4 : (z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2 = 1 := by
    calc
      (z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2 = (Real.sqrt ((z ^ 2 + 1).re ^ 2 + (z ^ 2 + 1).im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1 ^ 2 := by rw [h2]
      _ = (1 : ℝ) := by norm_num
  have eq5 : (z ^ 2 + 1).re = z.re ^ 2 - z.im ^ 2 + 1 := by
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring_nf <;> simp
    <;> ring
  have eq6 : (z ^ 2 + 1).im = 2 * z.re * z.im := by
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring_nf <;> simp
    <;> ring
  rw [eq5, eq6] at eq4
  have eq7 : z.re = 0 ∨ z.re = -1 / 2 := by
    have eq8 : z.re * (2 * z.re + 1) = 0 := by
      nlinarith [sq_nonneg (z.re), sq_nonneg (z.im), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    cases (mul_eq_zero.mp eq8) with
    | inl h => 
      left
      linarith
    | inr h => 
      right
      linarith
  cases eq7 with
  | inl h => 
    have eq8 : z.im = 0 := by
      rw [show z.re = (0 : ℝ) by linarith [h]] at eq3
      nlinarith
    left
    simp [Complex.ext_iff, h, eq8]
  | inr h => 
    have eq8 : z.im ^ 2 = 3 / 4 := by
      rw [show z.re = (-1 / 2 : ℝ) by linarith [h]] at eq3
      nlinarith
    have eq9 : z.im = Real.sqrt 3 / 2 ∨ z.im = - Real.sqrt 3 / 2 := by
      have h1 : z.im ^ 2 - (3 / 4 : ℝ) = 0 := by linarith
      have h4 : z.im ^ 2 - (3 / 4 : ℝ) = (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      rw [h4] at h1
      cases (mul_eq_zero.mp h1) with
      | inl h5 => 
        left
        linarith
      | inr h6 => 
        right
        nlinarith
    cases eq9 with
    | inl h_eq => 
      right
      right
      have eq11 : z = (-1 + Real.sqrt 3 * Complex.I) / 2 := by 
        have eq12 : z.re = -1 / 2 := by 
          linarith
        have eq13 : z.im = Real.sqrt 3 / 2 := by
          linarith [h_eq]
        simp [Complex.ext_iff, eq12, eq13]
        <;> ring_nf <;> norm_num [Complex.ext_iff]
        <;> try { nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] }
        <;> try { tauto }
        all_goals
        try { tauto }
      simp [eq11]
      <;> try { nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] }
      all_goals
      try { tauto }
      all_goals
      try { tauto }
      all_goals
      try { tauto }
      all_goals
      try { nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] }
      all_goals
      try { norm_num [Real.sqrt_nonneg 3] }
      all_goals
      try { nlinarith }
    | inr h_eq => 
      right
      left
      have eq10 : z = (-1 - Real.sqrt 3 * Complex.I) / 2 := by 
        have eq12 : z.re = -1 / 2 := by 
          linarith
        have eq13 : z.im = - Real.sqrt 3 / 2 := by
          linarith [h_eq]
        simp [Complex.ext_iff, eq12, eq13]
        <;> ring_nf <;> norm_num [Complex.ext_iff]
        <;> try { nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] }
        <;> try { tauto }
        all_goals
        try { tauto }
        all_goals
        try { tauto }
        all_goals
        try { tauto }
      simp [eq10]
      <;> try { nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] }
      all_goals
      try { tauto }
      all_goals
      try { tauto }
      all_goals
      try { tauto }
      all_goals
      try { nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)] }
      all_goals
      try { norm_num [Real.sqrt_nonneg 3] }
      all_goals
      try { nlinarith }