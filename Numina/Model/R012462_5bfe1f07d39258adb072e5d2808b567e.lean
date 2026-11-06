import Mathlib

open BigOperators Real Set

theorem algebra_321879 {f : ℝ → ℝ} (hf : f = λ x => x^3 - x^2 + 1)
  (M : ℝ) (hM : ∀ x ∈ Icc 1 2, ∃! y ∈ Icc 1 2, sqrt (f x * f y) = M) :
  M = sqrt 5 := by

  have h1 := hM 1 (by norm_num)
  rcases h1 with ⟨y1, ⟨hy1, hy1_unique⟩⟩

  have h3 : y1 ∈ Icc (1 : ℝ) 2 := by
    exact hy1.1
  have h2 : sqrt (f 1 * f y1) = M := by
    simpa using hy1.2

  have h4 : 1 ≤ y1 := by
    have h5 : y1 ∈ Icc (1 : ℝ) 2 := h3
    simp at h5 ⊢
    linarith

  have h5 : y1 ≤ 2 := by
    have h6 : y1 ∈ Icc (1 : ℝ) 2 := h3
    simp at h6 ⊢
    linarith

  have h6 : f 1 = 1 := by
    rw [hf]
    norm_num

  have h7 : f y1 ≥ 1 := by
    have h8 : y1 ≥ 1 := by linarith
    have h9 : y1 ≤ 2 := by linarith
    rw [hf]
    have h91 : (y1) ^ 3 - (y1) ^ 2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg (y1 - 1 : ℝ), sq_nonneg (y1 * (y1 - 1) : ℝ), sq_nonneg (y1 - 2 : ℝ)]
    simp at *
    all_goals linarith

  have h8 : sqrt (f 1 * f y1) = sqrt (f y1) := by
    have h9 : f 1 = 1 := h6
    rw [h9]
    all_goals
      ring_nf

  have h10 : sqrt (f y1) = M := by
    rw [h8] at h2
    linarith

  have h11 : f y1 = M ^ 2 := by
    calc
      f y1 = (sqrt (f y1)) ^ 2 := by
        rw [Real.sq_sqrt]
        have h13 : f y1 ≥ 0 := by linarith [h7]
        linarith
      _ = M ^ 2 := by
        rw [show sqrt (f y1) = M by linarith [h10]]

  have h9 := hM 2 (by norm_num)
  rcases h9 with ⟨y2, ⟨hy2, hy2_unique⟩⟩

  have h11 : y2 ∈ Icc (1 : ℝ) 2 := by
    exact hy2.1

  have h10 : sqrt (f 2 * f y2) = M := by
    simpa using hy2.2

  have h12 : 1 ≤ y2 := by
    have h13 : y2 ∈ Icc (1 : ℝ) 2 := h11
    simp at h13 ⊢
    linarith

  have h13 : y2 ≤ 2 := by
    have h14 : y2 ∈ Icc (1 : ℝ) 2 := h11
    simp at h14 ⊢
    linarith

  have h14 : f 2 = 5 := by
    rw [hf]
    norm_num

  have h15 : f y2 ≥ 1 := by
    have h16 : y2 ≥ 1 := by linarith
    have h17 : y2 ≤ 2 := by linarith
    rw [hf]
    have h19 : (y2) ^ 3 - (y2) ^ 2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg (y2 - 1 : ℝ), sq_nonneg (y2 * (y2 - 1) : ℝ), sq_nonneg (y2 - 2 : ℝ)]
    simp at *
    all_goals linarith

  have h17 : f 2 * f y2 = M ^ 2 := by
    calc
      f 2 * f y2 = (sqrt (f 2 * f y2)) ^ 2 := by
        rw [Real.sq_sqrt]
        have h180 : f 2 * f y2 ≥ 0 := by
          have h181 : f 2 ≥ 0 := by linarith [h14]
          have h182 : f y2 ≥ 0 := by linarith [h15]
          nlinarith
        linarith
      _ = M ^ 2 := by
        rw [show sqrt (f 2 * f y2) = M by linarith [h10]]

  have h181 : M ^ 2 ≥ 5 := by
    have h182 : 5 * f y2 = M ^ 2 := by
      have h183 : f 2 = 5 := h14
      rw [h183] at h17
      linarith
    have h183 : f y2 ≥ 1 := h15
    nlinarith

  have h183 : M ^ 2 ≤ 5 := by
    have h184 : f y1 ≤ 5 := by
      have h90 : y1 ≥ 1 := by linarith
      have h91 : y1 ≤ 2 := by linarith
      rw [hf]
      have h93 : (y1) ^ 3 - (y1) ^ 2 + 1 ≤ 5 := by
        nlinarith [sq_nonneg (y1 - 2 : ℝ), sq_nonneg (y1 * (y1 - 2) : ℝ), sq_nonneg (y1 - 1 : ℝ)]
      simp at *
      all_goals linarith
    have h185 : M ^ 2 ≤ 5 := by
      nlinarith [h11, h184]
    linarith

  have h184 : M ^ 2 = 5 := by
    nlinarith

  have h185 : M ≥ 0 := by
    have h186 : sqrt (f y1) = M := by linarith [h10]
    have h187 : sqrt (f y1) ≥ 0 := Real.sqrt_nonneg (f y1)
    linarith [h186, h187]

  have h188 : M = Real.sqrt 5 := by
    have h189 : M ≥ 0 := h185
    have h190 : M ^ 2 = 5 := h184
    have h191 : M = Real.sqrt 5 := by
      rw [← h190]
      field_simp [h189]
    linarith

  linarith [h188]