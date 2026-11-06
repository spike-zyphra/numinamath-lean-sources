import Mathlib

theorem algebra_242086 {F : ℂ → ℂ} (hF : ∀ z, z ≠ .I → F z = (z - .I) / (z + .I))
    (z : ℕ → ℂ) (h₀ : z 0 = 2016 + .I) (h : ∀ n, z (n + 1) = F (z n)) :
    z 2016 = 2016 + .I := by
  have h₁ (n : ℕ) : z (3 * n) = z 0 := by
    induction' n with n hn
    . simp
    . have g₀ : z (3 * n) ≠ .I := by
        simp [hn, h₀]
      have g₁ : z (3 * n) + .I ≠ 0 := by
        simp [hn, h₀, Complex.ext_iff]
      have g₂ : z (3 * n + 1) ≠ .I := by
        rw [h, hF _ g₀]
        field_simp [hn, h₀, Complex.ext_iff]
      have g₃ : z (3 * n + 1) + .I ≠ 0 := by
        rw [h, hF _ g₀]
        field_simp [hn, h₀, Complex.ext_iff]
      have g₄ : z (3 * n + 2) ≠ .I := by
        rw [h, hF _ g₂]
        field_simp
        rw [h, hF _ g₀]
        field_simp [hn, h₀, Complex.ext_iff]
        norm_num
      have g₅ : z (3 * n + 2) + .I ≠ 0 := by
        rw [h, hF _ g₂]
        field_simp
        rw [h, hF _ g₀]
        field_simp [hn, h₀, Complex.ext_iff]
      rw [mul_add_one, h, hF _ g₄]
      field_simp
      rw [h, hF _ g₂]
      field_simp
      rw [h, hF _ g₀]
      field_simp
      rw [hn, h₀]
      ring_nf
      rw [show 3 = 2 + 1 by norm_num, pow_add]
      field_simp
      ring
  rw [h₁ 672, h₀]