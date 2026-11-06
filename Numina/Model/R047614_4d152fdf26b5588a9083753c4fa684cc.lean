import Mathlib

theorem algebra_6831 {a b : ℂ} (h₀ : 2 * a + b = 2021) (h₁ : 2 * a ^ 2 + b ^ 2 = 2021) (h₂ : 2 * a ^ 3 + b ^ 3 = 2021) :
    False := by
  have h3 : b = 2021 - 2 * a := by 
    calc 
      b = 2 * a + b - 2 * a := by ring_nf 
      _ = 2021 - 2 * a := by rw [h₀]

  rw [show b = 2021 - 2 * a by exact h3] at h₁ h₂

  have eq3 : 6 * a ^ 2 - 4 * 2021 * a + 2021 ^ 2 - 2021 = 0 := by
    have h1' : 2 * a ^ 2 + (2021 - 2 * a) ^ 2 = 2021 := by 
      simpa using h₁
    calc 
      6 * a ^ 2 - 4 * 2021 * a + 2021 ^ 2 - 2021
        = (2 * a ^ 2 + (2021 - 2 * a) ^ 2) - 2021 := by ring_nf
      _ = 2021 - 2021 := by rw [h1']
      _ = 0 := by ring_nf

  have eq4 : 2 * a ^ 3 + (2021 - 2 * a) ^ 3 - 2021 = 0 := by
    have h2' : 2 * a ^ 3 + (2021 - 2 * a) ^ 3 = 2021 := by 
      simpa using h₂
    calc 
      2 * a ^ 3 + (2021 - 2 * a) ^ 3 - 2021 
        = (2 * a ^ 3 + (2021 - 2 * a) ^ 3) - 2021 := by ring_nf
      _ = 2021 - 2021 := by rw [h2']
      _ = 0 := by ring_nf

  norm_num [pow_two, pow_three, Complex.ext_iff] at eq3 eq4
  ring_nf at eq3 eq4 
  nlinarith [sq_nonneg (a.re - a.im), sq_nonneg (a.re + a.im), sq_nonneg (a.re * 2021 - a.im * 2021), sq_nonneg (a.re * a.im), sq_nonneg (a.re^2 - a.im^2), sq_nonneg (a.re), sq_nonneg (a.im)]