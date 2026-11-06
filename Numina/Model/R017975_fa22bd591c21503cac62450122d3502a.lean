import Mathlib

theorem algebra_15364 {i : ℂ} (hi : i^2 = -1) :
    Complex.abs ((1 + Real.sqrt 3 * i)^4) = 16 := by
  have h_abs : Complex.abs ((1 + Real.sqrt 3 * i) ^ 4) = Complex.abs (1 + Real.sqrt 3 * i) ^ 4 := by
    simp [Complex.abs_pow]
  have h_abs_val : Complex.abs (1 + Real.sqrt 3 * i) = 2 := by
    have h_eq : i.re * i.re - i.im * i.im = -1 := by
      have h_eq : i^2 = -1 := by assumption
      simp [Complex.ext_iff, pow_two] at h_eq ⊢
      all_goals try { tauto } <;> try { linarith } <;> try { nlinarith }
      all_goals try { tauto } <;> try { linarith } <;> try { nlinarith }
      all_goals try { nlinarith }
    have h_eq2 : i.re * i.im + i.im * i.re = 0 := by
      have h_eq : i^2 = -1 := by assumption
      simp [Complex.ext_iff, pow_two] at h_eq ⊢
      all_goals try { tauto } <;> try { linarith } <;> try { nlinarith }
      all_goals try { nlinarith } <;> try { tauto } <;> try { linarith }
      all_goals try { nlinarith }
    have h_eq3 : i.re ^ 2 + i.im ^ 2 = 1 := by
      nlinarith [sq_nonneg i.re, sq_nonneg i.im]
    have h_zero : i.re = 0 := by
      nlinarith [sq_nonneg (i.re * i.im), sq_nonneg (i.im), sq_nonneg (i.re)]
    have h_eq4 : i.im ^ 2 = 1 := by
      rw [h_zero] at h_eq
      nlinarith [sq_nonneg (i.im)]
    have h_sq : i.im ^ 2 = 1 := by
      nlinarith [sq_nonneg i.im, h_zero]
    have h_im_val : i.im = 1 ∨ i.im = -1 := by
      rw [sq_eq_one_iff] at h_sq
      tauto
    cases h_im_val with
    | inl h_eq1 =>
      have h_re_zero : i.re = 0 := h_zero
      have h_im_one : i.im = 1 := h_eq1
      simp [Complex.abs, Complex.normSq, h_re_zero, h_im_one, mul_comm, mul_add]
      <;> ring_nf <;> norm_num [Real.sqrt_eq_iff_sq_eq, Real.sq_sqrt] <;> try { nlinarith }
      <;> ring_nf <;> norm_num [Real.sqrt_eq_iff_sq_eq, Real.sq_sqrt] <;> try { nlinarith }
      all_goals try { nlinarith }
      <;> try { norm_num }
    | inr h_eq1 =>
      have h_re_zero : i.re = 0 := h_zero
      have h_im_neg : i.im = -1 := h_eq1
      simp [Complex.abs, Complex.normSq, h_re_zero, h_im_neg, mul_comm, mul_add]
      <;> ring_nf <;> norm_num [Real.sqrt_eq_iff_sq_eq, Real.sq_sqrt] <;> try { nlinarith }
      <;> ring_nf <;> norm_num [Real.sqrt_eq_iff_sq_eq, Real.sq_sqrt] <;> try { nlinarith }
      all_goals try { nlinarith }
      <;> try { norm_num }
  rw [h_abs, h_abs_val]
  all_goals norm_num
  all_goals norm_num [Real.sq_sqrt]
  all_goals try { norm_num }
  all_goals try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  all_goals try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  all_goals try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }
  all_goals try { norm_num }
  <;> try { norm_num [Real.sq_sqrt] }