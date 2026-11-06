import Mathlib

open Real

theorem inequalities_2358 (x y : ℝ) (hx : x ∈ Set.Ioc 0 1) (hy : y ∈ Set.Ioc 0 1) :
    2 > (1 - x) ^ y + (1 - y) ^ x := by
  rcases hx with ⟨hx_pos, hx_le⟩
  rcases hy with ⟨hy_pos, hy_le⟩
  have h1 : (1 - x : ℝ) ^ y < (1 : ℝ) := by
    have h4 : (1 - x : ℝ) < (1 : ℝ) := by linarith
    have h5 : (1 - x : ℝ) ≥ (0 : ℝ) := by linarith
    have h6 : (y : ℝ) > (0 : ℝ) := by linarith
    have h7 : (1 - x : ℝ) ^ y < (1 : ℝ) := by
      have h8 : (1 - x : ℝ) ^ y < ((1 : ℝ) : ℝ) := by
        have h9 : (1 - x : ℝ) < (1 : ℝ) := by linarith
        have h10 : (1 - x : ℝ) ≥ (0 : ℝ) := by linarith
        have h11 : (y : ℝ) > (0 : ℝ) := by linarith
        have h12 : (1 - x : ℝ) ^ y < ((1 : ℝ) : ℝ) ^ y := by
          apply Real.rpow_lt_rpow
          all_goals
            try linarith
        have h13 : ((1 : ℝ) : ℝ) ^ y = (1 : ℝ) := by
          simp
        have h14 : (1 - x : ℝ) ^ y < (1 : ℝ) := by
          nlinarith [h12, h13]
        linarith [h14]
      linarith [h8]
    linarith [h7]
  have h2 : (1 - y : ℝ) ^ x < (1 : ℝ) := by
    have h4 : (1 - y : ℝ) < (1 : ℝ) := by linarith
    have h5 : (1 - y : ℝ) ≥ (0 : ℝ) := by linarith
    have h6 : (x : ℝ) > (0 : ℝ) := by linarith
    have h7 : (1 - y : ℝ) ^ x < (1 : ℝ) := by
      have h8 : (1 - y : ℝ) ^ x < ((1 : ℝ) : ℝ) := by
        have h9 : (1 - y : ℝ) < (1 : ℝ) := by linarith
        have h10 : (1 - y : ℝ) ≥ (0 : ℝ) := by linarith
        have h11 : (x : ℝ) > (0 : ℝ) := by linarith
        have h12 : (1 - y : ℝ) ^ x < ((1 : ℝ) : ℝ) ^ x := by
          apply Real.rpow_lt_rpow
          all_goals
            try linarith
        have h13 : ((1 : ℝ) : ℝ) ^ x = (1 : ℝ) := by
          simp
        have h14 : (1 - y : ℝ) ^ x < (1 : ℝ) := by
          nlinarith [h12, h13]
        linarith [h14]
      linarith [h8]
    linarith [h7]
  have h3 : (1 - x : ℝ) ^ y + (1 - y : ℝ) ^ x < (2 : ℝ) := by
    linarith [h1, h2]
  linarith [h3]