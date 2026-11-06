import Mathlib

theorem algebra_13060 : (1 + Complex.I) ^ 2017 / (8 ^ 311 * 2 ^ 16 * 4 ^ 30) = 1 / 2 + 1 / 2 * Complex.I := by 
  have h1 : (1 + Complex.I) ^ 2017 = 2 ^ 1008 * (1 + Complex.I) := by
    have h2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      all_goals norm_num
    have h4 : ∀ (n : ℕ), (1 + Complex.I) ^ (2 * n + 1) = (1 + Complex.I) * (2 * Complex.I) ^ n := by 
      intro n
      induction n with
      | zero =>
        simp [pow_one]
        <;> ring_nf
      | succ n ih =>
        calc
          (1 + Complex.I) ^ (2 * (n + 1) + 1) 
            = (1 + Complex.I) ^ (2 * n + 1 + 2) := by ring_nf
          _ = (1 + Complex.I) ^ (2 * n + 1) * (1 + Complex.I) ^ 2 := by ring_nf
          _ = (1 + Complex.I) * (2 * Complex.I) ^ n * (2 * Complex.I) := by rw [ih, h2]
          _ = (1 + Complex.I) * (2 * Complex.I) ^ (n + 1) := by
            simp [pow_add] at *
            <;> ring_nf
    specialize h4 1008
    have h8 : (2 * Complex.I : ℂ) ^ 1008 = (2 : ℂ) ^ 1008 := by 
      have h9 : (2 * Complex.I : ℂ) ^ 4 = 16 := by
        norm_num [pow_succ, Complex.ext_iff, Complex.I_sq]
      have h10 : (2 * Complex.I : ℂ) ^ 1008 = ((2 * Complex.I : ℂ) ^ 4) ^ 252 := by 
        calc 
          (2 * Complex.I : ℂ) ^ 1008 = (2 * Complex.I : ℂ) ^ (4 * 252) := by norm_num 
          _ = ((2 * Complex.I : ℂ) ^ 4) ^ 252 := by rw [pow_mul]
      rw [h10, h9]
      all_goals norm_num [pow_succ]
    rw [h4, h8]
    all_goals ring_nf 
  have h2 : (8 ^ 311 * 2 ^ 16 * 4 ^ 30 : ℂ) = (2 : ℂ) ^ 1009 := by
    norm_num
  rw [h1, h2]
  have eq3 : (2 ^ 1008 * (1 + Complex.I) / (2 ^ 1009) ) =
      (1 / 2 + 1 / 2 * Complex.I) := by
    field_simp [show (2:ℂ)^1009 = 2 * (2:ℂ)^1008 by ring_nf]
    <;> ring_nf <;> norm_num
  simpa using eq3