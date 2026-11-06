import Mathlib

theorem algebra_168176 (x : ℝ) :
    8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 - Real.cos x + 1 = 0 ↔
    ∃ n : ℤ, x = 2 * Real.pi * n / 5 ∨ x = 2 * Real.pi * n / 3 := by 
  constructor
  · -- Forward: If $8 \cos^4 x - 8 \cos^2 x - \cos x + 1 = 0$, then $\exists n \in \mathbb{Z}, x = 2\pi n / 5 \lor x = 2\pi n / 3$
    intro h
    have h0 : Real.cos (4 * x) = 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1 := by
      have h1 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
        have h2 : Real.cos (4 * x) = Real.cos (2 * (2 * x)) := by ring_nf
        rw [h2]
        rw [Real.cos_two_mul]
      have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
        rw [Real.cos_two_mul]
      rw [h1, h2]
      nlinarith [Real.cos_sq_add_sin_sq x]
    have h0' : Real.cos (4 * x) - Real.cos x = 0 := by
      nlinarith [h, h0, Real.cos_sq_add_sin_sq x]
    have h0'' : Real.sin (5 * x / 2) * Real.sin (3 * x / 2) = 0 := by
      have h1 : Real.cos (4 * x) - Real.cos x = -2 * Real.sin (5 * x / 2) * Real.sin (3 * x / 2) := by
        rw [Real.cos_sub_cos]
        <;> ring_nf <;> field_simp <;> ring_nf
        all_goals norm_num [Real.sin_pi_div_three]
        all_goals ring_nf <;> field_simp
      nlinarith [h0']
    cases' (mul_eq_zero.mp h0'') with h4 h5
    · -- Case where $\sin(5x/2) = 0$
      have h6 : Real.sin (5 * x / 2) = 0 := h4
      have h7 : ∃ n : ℤ, 5 * x / 2 = n * Real.pi := by 
        rw [Real.sin_eq_zero_iff] at h6
        rcases h6 with ⟨n, hn⟩
        use n
        linarith
      rcases h7 with ⟨n, hn⟩
      have hn' : (5 * x) / 2 = n * Real.pi := by
        nlinarith [hn]
      have hn'' : x = 2 * Real.pi * n / 5 := by
        linarith
      use n
      left
      linarith
    · -- Case where $\sin(3x/2) = 0$
      have h6 : Real.sin (3 * x / 2) = 0 := h5
      have h7 : ∃ n : ℤ, 3 * x / 2 = n * Real.pi := by
        rw [Real.sin_eq_zero_iff] at h6
        rcases h6 with ⟨n, hn⟩
        use n
        linarith
      rcases h7 with ⟨n, hn⟩
      have hn' : (3 * x) / 2 = n * Real.pi := by
        nlinarith [hn]
      have hn'' : x = 2 * Real.pi * n / 3 := by
        linarith
      use n
      right
      linarith
  · -- Backward: If $\exists n \in \mathbb{Z}, x = 2\pi n / 5 \lor x = 2\pi n / 3$, then $8 \cos^4 x - 8 \cos^2 x - \cos x + 1 = 0$
    rintro ⟨n, hn⟩
    rcases hn with (h | h)
    · -- Case $x = 2 * Real.pi * n / 5$
      have h1 : x = 2 * Real.pi * n / 5 := h
      have h0 : Real.sin (5 * x / 2) = 0 := by
        have h2 : 5 * x / 2 = n * Real.pi := by
          nlinarith [h1]
        rw [h2]
        simp [Real.sin_eq_zero_iff]
      have h0' : Real.cos (4 * x) - Real.cos x = 0 := by
        have h1 : Real.cos (4 * x) - Real.cos x = -2 * Real.sin (5 * x / 2) * Real.sin (3 * x / 2) := by
          rw [Real.cos_sub_cos]
          <;> ring_nf <;> field_simp
          all_goals ring_nf
          all_goals norm_num [Real.sin_pi_div_three]
        have h0'' : Real.sin (5 * x / 2) = 0 := by assumption
        rw [h1, h0'']
        <;> ring_nf <;> norm_num [Real.sin_pi_div_three]
        all_goals nlinarith [Real.sin_sq_add_cos_sq x]
      have h0 : 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 - Real.cos x + 1 = 0 := by
        have h00 : Real.cos (4 * x) - Real.cos x = 0 := h0'
        have h000 : Real.cos (4 * x) = 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1 := by
          have h11 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
            have h22 : Real.cos (4 * x) = Real.cos (2 * (2 * x)) := by ring_nf
            rw [h22]
            rw [Real.cos_two_mul]
          have h22 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
            rw [Real.cos_two_mul]
          rw [h11, h22]
          nlinarith [Real.cos_sq_add_sin_sq x]
        nlinarith [h00, h000, Real.cos_sq_add_sin_sq x]
      linarith [h0]
    · -- Case $x = 2 * Real.pi * n / 3$
      have h2 : x = 2 * Real.pi * n / 3 := h
      have h0 : Real.sin (3 * x / 2) = 0 := by
        have h3 : 3 * x / 2 = n * Real.pi := by
          nlinarith [h2]
        rw [h3]
        simp [Real.sin_eq_zero_iff]
      have h0' : Real.cos (4 * x) - Real.cos x = 0 := by
        have h1 : Real.cos (4 * x) - Real.cos x = -2 * Real.sin (5 * x / 2) * Real.sin (3 * x / 2) := by
          rw [Real.cos_sub_cos]
          <;> ring_nf <;> field_simp
          all_goals ring_nf
          all_goals norm_num [Real.sin_pi_div_three]
        have h0'' : Real.sin (3 * x / 2) = 0 := by assumption
        rw [h1]
        rw [h0'']
        <;> ring_nf <;> norm_num [Real.sin_pi_div_three]
        all_goals nlinarith [Real.sin_sq_add_cos_sq x]
      have h0 : 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 - Real.cos x + 1 = 0 := by
        have h00 : Real.cos (4 * x) - Real.cos x = 0 := h0'
        have h000 : Real.cos (4 * x) = 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1 := by
          have h11 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
            have h22 : Real.cos (4 * x) = Real.cos (2 * (2 * x)) := by ring_nf
            rw [h22]
            rw [Real.cos_two_mul]
          have h22 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
            rw [Real.cos_two_mul]
          rw [h11, h22]
          nlinarith [Real.cos_sq_add_sin_sq x]
        nlinarith [h00, h000, Real.cos_sq_add_sin_sq x]
      linarith [h0]