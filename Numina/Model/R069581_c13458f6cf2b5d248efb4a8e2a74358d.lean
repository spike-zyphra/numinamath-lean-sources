import Mathlib

theorem number_theory_115011 (x : ℝ) (hx : x > 0) (h : ∃ r, x - ⌊x⌋ = r * ⌊x⌋ ∧ x - r * ⌊x⌋ = r ^ 2) :
    x = (1 + Real.sqrt 5) / 2 := by
  rcases h with ⟨r, ⟨h₁, h₂⟩⟩
  let n := ⌊x⌋
  have hn1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have hn2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have hfx : x - (n : ℝ) ≥ 0 := by linarith
  have hf2 : x - (n : ℝ) < 1 := by nlinarith
  have h₁' : x - (n : ℝ) = r * (n : ℝ) := by
    simpa [n] using h₁
  have h₂' : x - r * (n : ℝ) = r ^ 2 := by 
    simpa [n] using h₂
  have hn3 : (n : ℝ) = r ^ 2 := by
    nlinarith [h₁', h₂']
  have hn6 : n ≤ 1 := by
    have hn7 : (n : ℝ) ≤ (1 : ℝ) := by nlinarith [sq_nonneg (r - 1), sq_nonneg (x - 1), hn3 ]
    by_contra h8
    push_neg at h8
    have h9 : n ≥ 2 := by omega
    have : (n : ℝ) ≥ (2 : ℝ) := by
      have h10 : (n : ℝ) ≥ (2 : ℝ) := by
        have : n ≥ 2 := by omega
        exact_mod_cast this
      linarith
    linarith [hn7, this]
  have hn8 : n ≥ 1 := by
    by_contra h8
    push_neg at h8
    have h9 : n ≤ 0 := by omega
    have : (n : ℝ) ≤ (0 : ℝ) := by
      have : (n : ℝ) ≤ (0 : ℝ) := by
        have : n ≤ 0 := by omega
        exact_mod_cast this
      linarith
    nlinarith [sq_nonneg (r - 1), sq_nonneg (x - 1), hn3, this ]
  have hn9 : n = 1 := by
    omega
  have hn10 : (n : ℝ) = 1 := by
    exact_mod_cast hn9
  have hr2 : r ^ 2 = 1 := by
    nlinarith [hn3, hn10]
  have hr : r = 0 := by nlinarith [sq_nonneg (r - 1), hr2 ]
  nlinarith [sq_nonneg (x - 1), hn10, hr2, hf2, hn1, hn2 ]