import Mathlib

open Real Set
open scoped Real

theorem algebra_189228 (x : ℝ) :
  sin x ^ 4 + cos x ^ 4 = sin (2 * x) - 0.5 ↔
  ∃ n : ℤ, x = (4 * n + 1) * π / 4 := by
  constructor
  · -- Assume sin^4 x + cos^4 x = sin 2x - 0.5, prove that x = (4n+1)π/4 for some integer n
    intro h_eq
    have h1 : sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x * cos x) ^ 2 := by
      ring
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h3 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := by
      rw [h1, h2]
      all_goals ring
    have h4 : sin (2 * x) = 2 * sin x * cos x := by 
      rw [sin_two_mul]
    rw [h3, h4] at h_eq
    have h_eq3 : 2 * (sin x * cos x - 0.5) * (sin x * cos x + 1.5) = 0 := by 
      ring_nf at h_eq ⊢
      nlinarith
    cases' (mul_eq_zero.1 h_eq3) with h5 h6
    · 
      have h7 : sin x * cos x = 0.5 := by 
        nlinarith 
      have h8 : sin (2 * x) = 1 := by 
        have h9 : sin (2 * x) = 2 * sin x * cos x := by 
          rw [sin_two_mul]
        have h10 : sin x * cos x = 0.5 := h7
        rw [h9]
        linarith
      obtain ⟨n, hn⟩ := Real.sin_eq_one_iff.1 h8
      use n 
      field_simp at hn ⊢ 
      nlinarith
    · 
      -- Show that it is impossible
      have h8 : sin x * cos x = -1.5 := by 
        nlinarith
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x)]
  · -- Assume there exists an integer n such that x = (4n+1)π/4
    rintro ⟨n, hn⟩
    have h8 : 2 * x = Real.pi / 2 + 2 * n * Real.pi := by 
      rw [show x = (4 * n + 1) * Real.pi / 4 by 
        linarith [hn]
      ]
      ring_nf 
    have h9 : sin (2 * x) = 1 := by
      rw [show 2 * x = Real.pi / 2 + 2 * n * Real.pi by 
        linarith 
      ]
      have h_eq : sin (Real.pi / 2 + 2 * n * Real.pi) = 1 := by
        have h11 : sin (Real.pi / 2 + 2 * n * Real.pi) = sin (Real.pi / 2) := by 
          have : Real.pi / 2 + 2 * n * Real.pi = Real.pi / 2 + n * (2 * Real.pi) := by ring
          rw [this]
          rw [show sin (Real.pi / 2 + n * (2 * Real.pi)) = sin (Real.pi / 2) by 
            rw [show Real.pi / 2 + n * (2 * Real.pi) = Real.pi / 2 + n * (2 * Real.pi) by ring]
            rw [sin_add_int_mul_two_pi]
          ]
        rw [h11]
        norm_num 
      linarith [h_eq]
    -- sin x * cos x = 0.5 
    have h10 : sin x * cos x = 0.5 := by 
      have h11 : sin (2 * x) = 2 * sin x * cos x := by 
        rw [sin_two_mul]
      linarith 
    -- Prove the equation
    have h1 : sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x * cos x) ^ 2 := by 
      ring 
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
    have h3 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := by 
      rw [h1, h2] 
      all_goals ring 
    rw [h3, h9]
    rw [h10]
    all_goals 
      norm_num 
      <;> nlinarith 
      <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x)]