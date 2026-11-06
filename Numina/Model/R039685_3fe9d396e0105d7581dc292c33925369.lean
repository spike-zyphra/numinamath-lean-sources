import Mathlib

theorem algebra_127660 :
  IsLeast {x| ∃ (a b c d :ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a+2*b = 1 ∧ c + 2*d = 1 ∧ x = 1/a + 1/(b*c*d)} 25 := by

  constructor
  · -- 25 is in the set
    use 1 / 5, 2 / 5, 1 / 2, 1 / 4
    constructor
    · norm_num -- a > 0
    constructor
    · norm_num -- b > 0
    constructor
    · norm_num -- c > 0
    constructor
    · norm_num -- d > 0
    constructor
    · norm_num -- a + 2 * b = 1
    constructor
    · norm_num -- c + 2 * d = 1
    · norm_num -- x = 1/a + 1/(b*c*d)
  · -- No element less than 25 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h1, h2, h_eq⟩
    have h4 : 1/a + 1/(b * c * d) ≥ 25 := by
      have h5 : 0 < b := hb
      have h6 : 0 < c := hc
      have h7 : 0 < d := hd
      have h8 : a = 1 - 2 * b := by linarith
      have h9 : c = 1 - 2 * d := by linarith
      have h14 : (1 - 2 * b) > 0 := by nlinarith
      have h15 : (1 - 2 * d) > 0 := by nlinarith
      rw [show a = 1 - 2 * b by linarith, show c = 1 - 2 * d by linarith]
      have pos1 : 0 < (1 - 2 * b) := by nlinarith
      have pos2 : 0 < b := hb
      have pos3 : 0 < (1 - 2 * d) := by nlinarith
      have pos4 : 0 < d := hd
      have h20 : (1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) - 25) ≥ 0 := by
        have pos1 : 0 < (1 - 2 * b) := by nlinarith
        have pos2 : 0 < b := hb
        have pos3 : 0 < (1 - 2 * d) := by nlinarith
        have pos4 : 0 < d := hd
        have pos5 : 0 < b * (1 - 2 * d) * d := by positivity
        have h21 : 0 < (1 - 2 * b) * b * (1 - 2 * d) * d := by positivity
        have h22 : (1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) - 25) = ((b * (1 - 2 * d) * d + (1 - 2 * b) - 25 * (1 - 2 * b) * b * (1 - 2 * d) * d) / ((1 - 2 * b) * b * (1 - 2 * d) * d)) := by
          field_simp
          ring
        rw [h22]
        have h23 : 0 < (1 - 2 * b) * b * (1 - 2 * d) * d := by positivity
        have h24 : b * (1 - 2 * d) * d + (1 - 2 * b) - 25 * (1 - 2 * b) * b * (1 - 2 * d) * d ≥ 0 := by
          nlinarith [sq_nonneg (b - 2 / 5), sq_nonneg (d - 1 / 4),
          sq_nonneg ((1 - 2 * b) - 1 / 5), sq_nonneg ((1 - 2 * d) - 1 / 2),
          mul_pos hb (show 0 < 1 - 2 * b by nlinarith),
          mul_pos hb (show 0 < 1 - 2 * d by nlinarith),
          mul_pos (show 0 < 1 - 2 * d by nlinarith) hd,
          mul_pos hb hd
          ]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith [h_eq, h4]