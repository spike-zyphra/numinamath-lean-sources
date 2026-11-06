import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_11715 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = (sin x ^ 3 + 6 * sin x ^ 2 + sin x + 2 * (cos x) ^ 2 - 8) / (sin x - 1)) :
    {v : ℝ | ∃ x, (sin x - 1) ≠ 0 ∧ f x = v} = Ico 2 12 := by 
  ext1 v
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- Assume v is attained by some x with sinx ≠ 1
    rintro ⟨x, hx1, hfx⟩
    have hfx1 : f x = (sin x ^ 3 + 6 * sin x ^ 2 + sin x + 2 * (cos x) ^ 2 - 8) / (sin x - 1) := by
      apply h₀
    rw [hfx1] at hfx
    have h1 : sin x - 1 ≠ 0 := hx1
    have h2 : sin x < 1 := by
      by_contra h
      push_neg at h
      have h1' : sin x = 1 := by
        nlinarith [Real.sin_le_one x, h]
      have h2' : sin x - 1 = 0 := by
        linarith
      contradiction
    have h8 : (sin x ^3 + 6 * sin x ^ 2 + sin x + 2 * (cos x) ^ 2 - 8) / (sin x - 1) = sin x ^2 + 5 * sin x + 6 := by
      have h5 : sin x - 1 ≠ 0 := h1
      have h6 : sin x ^3 + 6 * sin x ^ 2 + sin x + 2 * (cos x) ^ 2 - 8 = (sin x ^2 + 5 * sin x + 6) * (sin x - 1) := by
        have hcos : (cos x) ^ 2 = 1 - sin x ^ 2 := by
          rw [Real.cos_sq']
        rw [hcos]
        nlinarith
      rw [h6]
      field_simp [h5]
      all_goals nlinarith
    rw [h8] at hfx
    constructor <;> nlinarith [sq_nonneg (sin x - 1), sq_nonneg (sin x + 1), Real.sin_le_one x, Real.neg_one_le_sin x, hfx, h2]
  · -- Assume v ∈ [2, 12)
    rintro ⟨hv1, hv2⟩
    have h41 : v ≥ 2 := by linarith
    have h42 : v < 12 := by linarith
    have h64 : ∃ s, -1 ≤ s ∧ s < 1 ∧ (s ^ 2 + 5 * s + 6 = v) := by
      use (-5 + Real.sqrt (1 + 4 * v) ) / 2
      constructor
      · -- Show -1 ≤ s
        nlinarith [Real.sqrt_nonneg (1 + 4 * (v)), Real.sq_sqrt (show 0 ≤ 1 + 4 * (v) by linarith)]
      constructor
      · -- Show s < 1
        nlinarith [Real.sqrt_nonneg (1 + 4 * (v)), Real.sq_sqrt (show 0 ≤ 1 + 4 * (v) by linarith)]
      · -- Show s ^ 2 + 5 * s + 6 = v
        nlinarith [Real.sqrt_nonneg (1 + 4 * (v)), Real.sq_sqrt (show 0 ≤ 1 + 4 * (v) by linarith)]
    rcases h64 with ⟨s, h112, h212, heq⟩
    use Real.arcsin s
    constructor
    · -- Show sin x - 1 ≠ 0
      have h17 : sin (Real.arcsin s) = s := by
        apply Real.sin_arcsin
        all_goals nlinarith
      have h171 : sin (Real.arcsin s) - 1 ≠ 0 := by
        rw [h17]
        linarith
      exact h171
    · -- Show f x = v
      have hfx1 : f (Real.arcsin s) = (sin (Real.arcsin s) ^ 3 + 6 * sin (Real.arcsin s) ^ 2 + sin (Real.arcsin s) + 2 * (cos (Real.arcsin s)) ^ 2 - 8) / (sin (Real.arcsin s) -1) := by
        apply h₀
      rw [hfx1]
      have h17 : sin (Real.arcsin s) = s := by
        apply Real.sin_arcsin
        all_goals nlinarith
      have h18 : cos (Real.arcsin s) ^ 2 = 1 - s ^ 2 := by
        have h21 : cos (Real.arcsin s) ^ 2 + sin (Real.arcsin s) ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq (Real.arcsin s)
        rw [h17] at h21
        linarith
      have h8 : (sin (Real.arcsin s) ^ 3 + 6 * sin (Real.arcsin s) ^ 2 + sin (Real.arcsin s) + 2 * (cos (Real.arcsin s)) ^ 2 - 8) / (sin (Real.arcsin s) - 1) = s ^2 + 5 * s + 6 := by
        rw [h17, h18]
        have h40 : s - 1 ≠ 0 := by
          nlinarith
        field_simp [h40]
        nlinarith
      rw [h8]
      linarith