import Mathlib

theorem algebra_166835 {x y : ℂ} (h₀ : x + y = Real.sqrt 20) (h₁ : x ^ 2 + y ^ 2 = 15) :
    Complex.abs (x - y) = Real.sqrt 10 := by
  have h2 : (x + y) ^ 2 = (20 : ℂ) := by
    rw [h₀]
    have h3 : ((Real.sqrt 20 : ℝ) : ℂ) ^ 2 = (20 : ℂ) := by
      simp [pow_two, Complex.ext_iff, mul_add, add_mul]
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
      all_goals norm_num
    simpa using h3
  have h4 : x * y = (5 / 2 : ℂ) := by
    have eq1 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by
      ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring
    rw [h2, h₁] at eq1
    simp [Complex.ext_iff] at eq1 ⊢
    constructor
    · -- Real part
      linarith
    · -- Imaginary part
      linarith
  have h5 : (x - y) ^ 2 = (10 : ℂ) := by
    have eq1 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by
      ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring_nf
      <;> simp [Complex.ext_iff, pow_two]
      <;> ring
    rw [eq1, h2, h4]
    norm_num [Complex.ext_iff, pow_two]
    <;> norm_num [Complex.ext_iff, pow_two]
    all_goals norm_num
    all_goals norm_num [Real.sq_sqrt]
    all_goals norm_num
  have h6 : (x - y) ^ 2 = (10 : ℂ) := h5
  have h7 : Complex.abs (x - y) = Real.sqrt 10 := by
    have h8 : (x - y) ^ 2 = (10 : ℂ) := h6
    have h9 : Complex.abs ((x - y) ^ 2) = Complex.abs (10 : ℂ) := by 
      rw [h8]
    have h10 : Complex.abs ((x - y) ^ 2) = Complex.abs (x - y) ^ 2 := by
      simp [Complex.abs_pow]
    have h11 : Complex.abs (10 : ℂ) = (10 : ℝ) := by
      simp [Complex.abs, Complex.normSq]
      <;> norm_num
    -- Combine to get Complex.abs (x - y) ^ 2 = 10
    have h14 : Complex.abs (x - y) ^ 2 = (10 : ℝ) := by
      rw [h10] at h9
      rw [h11] at h9
      norm_num at h9 ⊢
      try { exact_mod_cast h9 }
      all_goals norm_num
    have h12 : Complex.abs (x - y) ≥ 0 := by
      positivity
    -- Take the square root
    have h15 : Complex.abs (x - y) = Real.sqrt 10 := by
      have h16 : Complex.abs (x - y) ^ 2 = (10 : ℝ) := h14
      have h17 : Real.sqrt (Complex.abs (x - y) ^ 2) = Real.sqrt (10 : ℝ) := by
        rw [h16]
      have h18 : Real.sqrt (Complex.abs (x - y) ^ 2) = Complex.abs (x - y) := by
        rw [Real.sqrt_sq (by linarith)]
      have h19 : Complex.abs (x - y) = Real.sqrt (10 : ℝ) := by
        linarith [h17, h18]
      exact_mod_cast h19
    exact_mod_cast h15
  exact h7