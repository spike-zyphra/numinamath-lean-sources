import Mathlib

theorem algebra_4640
    {F : ℝ → ℝ}
    (hF1 : ∀ x, 0 ≤ x ∧ x ≤ 1 → F (x / 3) = F x / 2)
    (hF2 : ∀ x, 0 ≤ x ∧ x ≤ 1 → F (1 - x) = 1 - F x)
    (hF3 : AntitoneOn F (Set.Icc 0 1)):
    F (1 / 13) = 1 / 7 := by
  have h1 := hF1 0 (by norm_num)
  norm_num at h1
  have h2 := hF2 0 (by norm_num)
  norm_num at h2
  have h3 := hF1 1 (by norm_num)
  norm_num at h3
  have h4 := hF2 (1 / 3) (by norm_num)
  have h5 := hF1 (2 / 3) (by norm_num)
  norm_num at h4
  norm_num at h5
  have h6 := hF1 (3 / 13) (by norm_num)
  have h7 := hF2 (1 / 13) (by norm_num)
  have h8 := hF2 (3 / 13) (by norm_num)
  have h9 := hF2 (10 / 13) (by norm_num)
  have h10 := hF1 (9 / 13) (by norm_num)
  have h11 := hF2 (4 / 13) (by norm_num)
  have h13 := hF1 (12 / 13) (by norm_num)
  have h14 := hF2 (9 / 13) (by norm_num)
  norm_num at h6 h7 h8 h9 h10 h11 h13 h14
  linarith