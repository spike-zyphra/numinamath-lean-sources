import Mathlib

theorem algebra_245405 (a b c : ℝ) (h₀ : a + b + c = 2) (h₁ : a^2 + b^2 + c^2 = 6) (h₂ : a^3 + b^3 + c^3 = 8) :
    ∃ n, a^n + b^n + c^n = 2^2017 := by

  have h3 : a * b + a * c + b * c = -1 := by
    have eq1 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by 
      ring
    rw [h₀, h₁] at eq1
    linarith

  have h4 : a * b * c = -2 := by 
    have eq1 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by 
      ring
    rw [h₀, h₁, h3] at eq1
    linarith [h₂, eq1]

  have h5 : (a) ^ 3 - 2 * (a) ^ 2 - (a) + 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      h₀, h3, h4, h₁, h₂
    ]

  have h6 : (a + 1) * (a - 1) * (a - 2) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h6) with h7 h8
  cases' (mul_eq_zero.mp h7) with h9 h10

  · -- Case where $a + 1 = 0$, so $a = -1$
    have ha1 : a = -1 := by linarith 
    have hsum1 : b + c = 3 := by 
      linarith [h₀, ha1]
    have hprod1 : b * c = 2 := by
      have h3' : a * b + a * c + b * c = -1 := h3
      rw [ha1] at h3'
      nlinarith

    have h11 : (b - 1) * (b - 2) = 0 := by 
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b - 2), 
        hsum1, hprod1 
      ]

    cases' (mul_eq_zero.mp h11) with hb1 hb2

    · -- Case b = 1 
      have hb1' : b = 1 := by linarith 
      have hc1' : c = 2 := by linarith [hsum1, hb1']
      use 2017 
      norm_num [ha1, hb1', hc1']

    · -- Case b = 2 
      have hb2' : b = 2 := by linarith 
      have hc2' : c = 1 := by linarith [hsum1, hb2']
      use 2017 
      norm_num [ha1, hb2', hc2']

  · -- Case where $a - 1 = 0$, so $a = 1$
    have ha1 : a = 1 := by linarith 
    have hsum1 : b + c = 1 := by 
      linarith [h₀, ha1]
    have hprod1 : b * c = -2 := by 
      have h3' : a * b + a * c + b * c = -1 := h3
      rw [ha1] at h3'
      nlinarith

    have h11 : (b - 2) * (b + 1) = 0 := by
      nlinarith [sq_nonneg (b - 2), sq_nonneg (b + 1), 
        hsum1, hprod1 
      ]

    cases' (mul_eq_zero.mp h11) with hb1 hb2

    · -- Case b = 2 
      have hb1' : b = 2 := by linarith 
      have hc1' : c = -1 := by linarith [hsum1, hb1']
      use 2017 
      norm_num [ha1, hb1', hc1']

    · -- Case b = -1 
      have hb2' : b = -1 := by linarith 
      have hc2' : c = 2 := by linarith [hsum1, hb2']
      use 2017 
      norm_num [ha1, hb2', hc2']

  · -- Case where $a - 2 = 0$, so $a = 2$
    have ha1 : a = 2 := by linarith 
    have hsum1 : b + c = 0 := by 
      linarith [h₀, ha1]
    have hprod1 : b * c = -1 := by
      have h3' : a * b + a * c + b * c = -1 := h3
      rw [ha1] at h3'
      nlinarith

    have h11 : (b + 1) * (b - 1) = 0 := by
      nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1), 
        hsum1, hprod1 
      ]

    cases' (mul_eq_zero.mp h11) with hb1 hb2

    · -- Case b = -1 
      have hb1' : b = -1 := by linarith 
      have hc1' : c = 1 := by linarith [hsum1, hb1']
      use 2017 
      norm_num [ha1, hb1', hc1']

    · -- Case b = 1 
      have hb2' : b = 1 := by linarith 
      have hc2' : c = -1 := by linarith [hsum1, hb2']
      use 2017 
      norm_num [ha1, hb2', hc2']