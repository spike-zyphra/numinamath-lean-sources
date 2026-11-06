import Mathlib

theorem algebra_318255 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f x = 1 / a - 1 / (a ^ x + 1)) :
    ∀ x, f x ∈ Set.Ioo (-1 / 2) (1 / 2) := by
  have h1 : a = 2 := by
    have h0 : f 0 = 0 := by
      specialize hodd 0
      norm_num at hodd
      linarith
    rw [hf 0] at h0
    have h1' : (a ^ (0 : ℝ) : ℝ) = 1 := by
      simp
    rw [h1'] at h0
    field_simp at h0 ⊢
    all_goals nlinarith
  intro x
  rw [hf x]
  rw [h1]
  have h2 : (2 : ℝ) ^ x > 0 := by positivity
  have h3 : (2 : ℝ) ^ x + 1 > 1 := by
    linarith [h2]
  have h4 : 0 < ( (2 : ℝ) ^ x + 1 ) := by
    linarith [h2]
  constructor
  · -- Show that -1/2 < f(x)
    have h5 : (1 / (2 : ℝ) - 1 / ((2 : ℝ) ^ x + 1) ) > -1 / 2 := by
      have h10 : (1 / ((2 : ℝ) ^ x + 1) ) < 1 := by
        have h11 : ((2 : ℝ) ^ x + 1 ) > 1 := h3
        have h12 : (1 / ((2 : ℝ) ^ x + 1) ) < 1 := by
          apply (div_lt_iff₀ (by linarith)).mpr
          nlinarith
        linarith
      nlinarith
    norm_num at h5 ⊢
    all_goals linarith
  · -- Show that f(x) < 1/2
    have h8 : (1 / (2 : ℝ) - 1 / ((2 : ℝ) ^ x + 1) ) < (1 / 2 : ℝ) := by
      have h10 : (1 / ((2 : ℝ) ^ x + 1) ) > 0 := by
        apply div_pos
        norm_num
        all_goals linarith [show 0 < ( (2 : ℝ) ^ x ) from by positivity ]
      nlinarith
    norm_num at h8 ⊢
    all_goals linarith