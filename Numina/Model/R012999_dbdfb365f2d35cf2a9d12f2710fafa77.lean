import Mathlib

theorem algebra_165998 (s r c : ℝ) (h₀ : s > 0) (h₁ : r > 0) (h₂ : c > 0)
    (h₃ : r = 5 * s) (h₄ : c = 2.5 * r) (h₅ : 1.5 / s + 10 / r = 40 / c + 6) :
    1.5 / s + 40 / c + 10 / r = 134 := by

  have h₆ : c = 12.5 * s := by 
    rw [h₄, h₃]
    ring_nf
  have eq1 : 10 / r = 2 / s := by 
    rw [h₃]
    field_simp
    <;> ring_nf 
  have eq2 : 40 / c = 3.2 / s := by
    rw [h₆]
    field_simp
    <;> ring_nf 
  have h₇ : s = (0.05 : ℝ) := by
    have eq3 : 1.5 / s + 2 / s = 3.2 / s + 6 := by 
      have eq5' : 10 / r = 2 / s := eq1
      have eq6' : 40 / c = 3.2 / s := eq2
      have eq7 : 1.5 / s + 10 / r = 40 / c + 6 := h₅
      rw [eq5'] at eq7
      rw [eq6'] at eq7
      linarith 
    have eq4 : (1.5 / s + 2 / s : ℝ) = (3.5 / s : ℝ) := by 
      have h11 : s ≠ 0 := by linarith
      have eq14 : (1.5 + (2 : ℝ)) = (3.5 : ℝ) := by norm_num
      have eq15 : (1.5 / s + 2 / s : ℝ) = (3.5 / s : ℝ) := by 
        have eq16 : (1.5 / s + 2 / s : ℝ) = ((1.5 + (2 : ℝ)) / s : ℝ) := by 
          field_simp [(show s ≠ 0 by linarith)]
        rw [eq16]
        rw [eq14]
      exact_mod_cast eq15
    -- So we have 3.5 / s = 3.2 / s + 6
    have eq6 : (3.5 / s : ℝ) = (3.2 / s + 6 : ℝ) := by
      linarith [eq4, eq3]
    have eq7 : (3.5 / s : ℝ) - (3.2 / s : ℝ) = (6 : ℝ) := by
      linarith [eq6]
    have eq8 : (3.5 / s : ℝ) - (3.2 / s : ℝ) = (0.3 / s : ℝ) := by
      have h11 : s ≠ 0 := by linarith
      have eq15 : (3.5 - (3.2 : ℝ)) = (0.3 : ℝ) := by norm_num
      have eq16 : (3.5 / s : ℝ) - (3.2 / s : ℝ) = (0.3 / s : ℝ) := by 
        have eq17 : (3.5 / s - 3.2 / s : ℝ) = ((3.5 - (3.2 : ℝ)) / s : ℝ) := by 
          field_simp [(show s ≠ 0 by linarith)]
        rw [eq17]
        rw [eq15]
      exact_mod_cast eq16
    -- Therefore 0.3 / s = 6
    have eq9 : (0.3 / s : ℝ) = (6 : ℝ) := by
      linarith [eq7, eq8]
    -- From 0.3 / s = 6, we need to solve for s
    have h10 : s * (6 : ℝ) = (0.3 : ℝ) := by
      have h11 : s ≠ 0 := by linarith
      -- Solving equation 0.3 / s = 6 for s
      have h_eq1 : (0.3 / s : ℝ) = (6 : ℝ) := eq9
      -- Transform to 0.3 = 6 * s
      have eq11 : s * (6 : ℝ) = (0.3 : ℝ) := by
        have h11 : s ≠ 0 := by linarith
        field_simp [(show s ≠ 0 by linarith)] at h_eq1 ⊢
        all_goals nlinarith [h_eq1, show s > 0 by linarith]
      exact_mod_cast eq11
    -- Solving equation 0.3 / s = 6 for s = 0.05
    have h11 : s = (0.05 : ℝ) := by
      norm_num at h10 ⊢ 
      linarith
    exact_mod_cast h11
  -- From h₇ = 0.05:
  have h₈ : r = (0.25 : ℝ) := by
    rw [h₃, h₇]
    norm_num
  have h₉ : c = (0.625 : ℝ) := by
    rw [h₆, h₇]
    norm_num 
  have ht1 : 1.5 / s = (30 : ℝ) := by
    rw [h₇]
    norm_num
  have ht2 : 40 / c = (64 : ℝ) := by
    rw [h₉]
    norm_num
  have ht3 : 10 / r = (40 : ℝ) := by 
    rw [h₈]
    norm_num
  -- Computing: 30 + 64 + 40
  -- The total time is 134 minutes.
  linarith [ht1, ht2, ht3]