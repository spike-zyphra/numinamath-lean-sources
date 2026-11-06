import Mathlib

open Real Set


theorem algebra_5026 {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    (cos θ)^8 + (sin θ)^8 = 17 / 32 ↔
    ∃ n : ℤ, θ = ((2 * n - 1) * π) / 8 := by
  rcases hθ with ⟨h1, h2⟩
  constructor
  · -- Assume (cos θ)^8 + (sin θ)^8 = 17 / 32, prove ∃ n : ℤ, θ = ((2 * n - 1) * π) / 8
    intro h
    have h3 : cos (4 * θ) = 0 := by
      have h4 : (cos θ) ^ 8 + (sin θ) ^ 8 = (cos (4 * θ) ^ 2 + 14 * cos (4 * θ) + 17) / 32 := by
        have h1 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
          rw [show 4 * θ = 2 * (2 * θ) by ring]
          rw [cos_two_mul]
        have h2 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := by
          rw [cos_two_mul]
        have h3 : cos (2 * θ) = 1 - 2 * sin θ ^ 2 := by
          rw [cos_two_mul, sin_sq]
          ring
        have h4 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq θ
        have h7 : cos θ ^ 2 * sin θ ^ 2 = (1 - cos (4 * θ)) / 8 := by
          have h12 : sin (2 * θ) = 2 * sin θ * cos θ := by
            rw [sin_two_mul]
          have h13 : cos (4 * θ) = 1 - 2 * (sin (2 * θ) ^ 2) := by
            rw [show 4 * θ = 2 * (2 * θ) by ring]
            rw [cos_two_mul, sin_sq]
            ring
          rw [h13, h12]
          nlinarith
        have h5 : (cos θ) ^ 4 + (sin θ) ^ 4 = 1 - 2 * (cos θ ^ 2 * sin θ ^ 2) := by
          calc
            (cos θ) ^ 4 + (sin θ) ^ 4 = ((cos θ ^ 2 + sin θ ^ 2) ^ 2 - 2 * (cos θ ^ 2 * sin θ ^ 2)) := by ring
            _ = (1 ^ 2 - 2 * (cos θ ^ 2 * sin θ ^ 2)) := by rw [h4]
            _ = 1 - 2 * (cos θ ^ 2 * sin θ ^ 2) := by ring
        have h6 : (cos θ) ^ 8 + (sin θ) ^ 8 = ((cos θ ^ 4 + sin θ ^ 4) ^ 2 - 2 * (cos θ ^ 4 * sin θ ^ 4)) := by ring
        have h10 : (cos θ) ^ 4 * (sin θ) ^ 4 = (cos θ ^ 2 * sin θ ^ 2) ^ 2 := by
          ring
        rw [h6, h5, h10, h7]
        ring_nf
      rw [h4] at h
      have h5 : cos (4 * θ) ^ 2 + 14 * cos (4 * θ) + 17 = 17 := by
        linarith
      have h6 : cos (4 * θ) ^ 2 + 14 * cos (4 * θ) = 0 := by
        linarith
      have h7 : cos (4 * θ) * (cos (4 * θ) + 14) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- cos(4θ) = 0.
        linarith
      · -- cos(4θ) + 14 = 0.
        have h10 : cos (4 * θ) = -14 := by
          linarith
        have h11 : cos (4 * θ) ≥ -1 := by
          have h14 : cos (4 * θ) ≥ -1 := by
            linarith [neg_one_le_cos (4 * θ), cos_le_one (4 * θ)]
          linarith
        linarith
    have h4 : ∃ k : ℤ, 4 * θ = (Real.pi / 2) + ↑k * Real.pi := by
      rw [cos_eq_zero_iff] at h3
      obtain ⟨k, hk⟩ := h3
      use k
      all_goals
        try linarith
    rcases h4 with ⟨k, hk⟩
    use k + 1
    have hk2 : θ = ((2 * (k : ℝ) + 1) * Real.pi) / 8 := by
      nlinarith [hk]
    have hk5 : ((2 * (k : ℝ) + 1) * Real.pi) / 8 = ((2 * ((k + 1 : ℤ) : ℝ) - 1) * Real.pi) / 8 := by
      simp at *
      all_goals
      ring_nf
    linarith [hk2, hk5]
  · -- Assume ∃ n : ℤ, θ = ((2 * n - 1) * π) / 8, prove (cos θ)^8 + (sin θ)^8 = 17 / 32
    rintro ⟨n, hn⟩
    have h3 : cos (4 * θ) = 0 := by
      have h4 : 4 * θ = ((2 * n - 1) * Real.pi) / 2 := by
        have h5 : θ = ((2 * n - 1) * Real.pi) / 8 := by
          linarith [hn]
        linarith
      rw [h4]
      have h6 : cos (((2 * (n : ℝ) - 1) * Real.pi) / 2) = 0 := by
        have h7 : ((2 * (n : ℝ) - 1) * Real.pi) / 2 = (n : ℝ) * Real.pi - Real.pi / 2 := by
          ring_nf
        rw [h7]
        have h8 : cos ((↑n * Real.pi - Real.pi / 2)) = 0 := by
          have h11 : cos ((↑n * Real.pi - Real.pi / 2)) = cos (↑n * Real.pi) * cos (Real.pi / 2) + sin (↑n * Real.pi) * sin (Real.pi / 2) := by
            rw [cos_sub]
          rw [h11]
          have h12 : cos (Real.pi / 2) = 0 := by
            exact cos_pi_div_two
          have h13 : sin (Real.pi / 2) = 1 := by
            exact sin_pi_div_two
          rw [h12, h13]
          have h14 : sin (↑n * Real.pi) = 0 := by
            have : sin (↑n * Real.pi) = 0 := by
              simp [Real.sin_int_mul_pi]
            linarith
          nlinarith
        linarith
      linarith
    have h4 : (cos θ) ^ 8 + (sin θ) ^ 8 = (cos (4 * θ) ^ 2 + 14 * cos (4 * θ) + 17) / 32 := by
      have h1 : cos (4 * θ) = 2 * cos (2 * θ) ^ 2 - 1 := by
        rw [show 4 * θ = 2 * (2 * θ) by ring]
        rw [cos_two_mul]
      have h2 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := by
        rw [cos_two_mul]
      have h3 : cos (2 * θ) = 1 - 2 * sin θ ^ 2 := by
        rw [cos_two_mul, sin_sq]
        ring
      have h4 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq θ
      have h7 : cos θ ^ 2 * sin θ ^ 2 = (1 - cos (4 * θ)) / 8 := by
        have h12 : sin (2 * θ) = 2 * sin θ * cos θ := by
          rw [sin_two_mul]
        have h13 : cos (4 * θ) = 1 - 2 * (sin (2 * θ) ^ 2) := by
          rw [show 4 * θ = 2 * (2 * θ) by ring]
          rw [cos_two_mul, sin_sq]
          ring
        rw [h13, h12]
        nlinarith
      have h5 : (cos θ) ^ 4 + (sin θ) ^ 4 = 1 - 2 * (cos θ ^ 2 * sin θ ^ 2) := by
        calc
          (cos θ) ^ 4 + (sin θ) ^ 4 = ((cos θ ^ 2 + sin θ ^ 2) ^ 2 - 2 * (cos θ ^ 2 * sin θ ^ 2)) := by ring
          _ = (1 ^ 2 - 2 * (cos θ ^ 2 * sin θ ^ 2)) := by rw [h4]
          _ = 1 - 2 * (cos θ ^ 2 * sin θ ^ 2) := by ring
      have h6 : (cos θ) ^ 8 + (sin θ) ^ 8 = ((cos θ ^ 4 + sin θ ^ 4) ^ 2 - 2 * (cos θ ^ 4 * sin θ ^ 4)) := by ring
      have h10 : (cos θ) ^ 4 * (sin θ) ^ 4 = (cos θ ^ 2 * sin θ ^ 2) ^ 2 := by
        ring
      rw [h6, h5, h10, h7]
      ring_nf
    rw [h4, h3]
    all_goals norm_num