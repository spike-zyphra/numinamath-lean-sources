import Mathlib

theorem algebra_9040 (a : ℝ) (f : ℝ → ℝ) (hf : f = fun x => abs (Real.sin x ^ 2 - 4 * Real.sin x - a)) : IsGreatest (Set.image f {x | x ∈ Set.univ}) 4 ↔ a = 1 := by
  constructor
  · -- If 4 is the greatest element in the image, then a = 1
    intro h
    have h1 : 4 ∈ Set.image f {x | x ∈ Set.univ} := h.1
    rcases h1 with ⟨x, hx, hfx⟩
    have hx' : x ∈ Set.univ := hx
    have h2 : f x = 4 := by
      simpa using hfx
    rw [hf] at h2
    simp at h2
    have h4 : ∀ y, y ∈ Set.image f {x | x ∈ Set.univ} → y ≤ 4 := by
      apply h.2
    have h5 : (abs (Real.sin (Real.pi / 2) ^ 2 - 4 * Real.sin (Real.pi / 2) - a) : ℝ) ≤ 4 := by
      have h6 : abs (Real.sin (Real.pi / 2) ^ 2 - 4 * Real.sin (Real.pi / 2) - a) ∈ Set.image f {x | x ∈ Set.univ} := by
        use Real.pi / 2
        all_goals
          simp [hf]
      have h7 : abs (Real.sin (Real.pi / 2) ^ 2 - 4 * Real.sin (Real.pi / 2) - a) ≤ 4 := by
        apply h4 (abs (Real.sin (Real.pi / 2) ^ 2 - 4 * Real.sin (Real.pi / 2) - a)) h6
      linarith
    have h6 : (abs (Real.sin (3 * Real.pi / 2) ^ 2 - 4 * Real.sin (3 * Real.pi / 2) - a) : ℝ) ≤ 4 := by
      have h7 : abs (Real.sin (3 * Real.pi / 2) ^ 2 - 4 * Real.sin (3 * Real.pi / 2) - a) ∈ Set.image f {x | x ∈ Set.univ} := by
        use 3 * Real.pi / 2
        all_goals
          simp [hf]
      have h8 : abs (Real.sin (3 * Real.pi / 2) ^ 2 - 4 * Real.sin (3 * Real.pi / 2) - a) ≤ 4 := by
        apply h4 (abs (Real.sin (3 * Real.pi / 2) ^ 2 - 4 * Real.sin (3 * Real.pi / 2) - a)) h7
      linarith
    have h7 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have h8 : Real.sin (3 * Real.pi / 2) = -1 := by
      have : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
      rw [this]
      rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
      norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
    have h9 : abs ((Real.sin (Real.pi / 2) : ℝ) ^ 2 - 4 * Real.sin (Real.pi / 2) - a) = abs (-3 - a) := by
      rw [h7]
      norm_num
    have h10 : abs ((Real.sin (3 * Real.pi / 2) : ℝ) ^ 2 - 4 * Real.sin (3 * Real.pi / 2) - a) = abs (5 - a) := by
      rw [h8]
      norm_num
    rw [h9] at h5
    rw [h10] at h6
    cases eq_or_eq_neg_of_abs_eq h2 with
    | inl h_eq4 =>
      nlinarith [abs_le.mp h5, abs_le.mp h6, Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1)]
    | inr h_eq_neg4 =>
      nlinarith [abs_le.mp h5, abs_le.mp h6, Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1)]
  · -- If a = 1, prove 4 is the greatest element in the image
    intro h
    rw [h] at hf
    constructor
    · -- Show 4 is in the image
      use Real.pi / 2
      all_goals
        simp [hf]
        <;> norm_num [Real.sin_pi_div_two]
    · -- Show 4 is the greatest element in the image
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      simp [hf] at hfx
      have h11 : -1 ≤ Real.sin x := Real.neg_one_le_sin x
      have h12 : Real.sin x ≤ 1 := Real.sin_le_one x
      have h13 : Real.sin x ^ 2 - 4 * Real.sin x - (1 : ℝ) ≤ 4 := by
        nlinarith [sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1), Real.sin_sq_add_cos_sq x]
      have h14 : Real.sin x ^ 2 - 4 * Real.sin x - (1 : ℝ) ≥ -4 := by
        nlinarith [sq_nonneg (Real.sin x - 1), sq_nonneg (Real.sin x + 1), Real.sin_sq_add_cos_sq x]
      have h15 : abs (Real.sin x ^ 2 - 4 * Real.sin x - (1 : ℝ)) ≤ 4 := by
        apply abs_le.mpr
        constructor
        · linarith
        · linarith
      linarith [h15, hfx]