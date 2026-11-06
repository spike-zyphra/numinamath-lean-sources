import Mathlib

theorem algebra_317515 {a b c M N P : ℝ} (ha : 0 < a) (hb : b < 0) (hc : c < b)
    (h : a + b + c = 1) (hM : M = (b + c) / a) (hN : N = (a + c) / b)
    (hP : P = (a + b) / c) : M > P ∧ P > N := by
  constructor
  · -- Show M > P
    rw [hM, hP]
    have h1 : (b + c) / a - (a + b) / c > 0 := by
      have h2 : (b + c) / a - (a + b) / c = ((b + c) * c - (a + b) * a) / (a * c) := by
        have ha' : a ≠ 0 := by linarith
        have hc' : c ≠ 0 := by nlinarith
        field_simp [ha', hc']
        <;> ring
      rw [h2]
      have h3 : (b + c) * c - (a + b) * a = (c - a) * (a + b + c) := by
        nlinarith
      have h6 : a * c < 0 := by
        apply mul_neg_of_pos_of_neg
        all_goals nlinarith
      have h7 : (c - a) * (a + b + c) < 0 := by
        have h8 : a + b + c = 1 := by linarith
        rw [h8]
        have h9 : c - a < 0 := by nlinarith
        nlinarith
      have h4 : ((b + c) * c - (a + b) * a) / (a * c) > 0 := by
        apply div_pos_of_neg_of_neg
        linarith [h7]
        nlinarith [h6]
      linarith [h4]
    linarith [h1]
  · -- Show P > N
    rw [hP, hN]
    have h4 : a + b = 1 - c := by linarith
    have h5 : b < 0 := hb
    have h6 : c < 0 := by nlinarith
    have h7 : (a + b) / c - (a + c) / b > 0 := by
      have h8 : (a + b) / c - (a + c) / b = ( (a + b) * b - (a + c) * c ) / (c * b) := by
        have hc' : c ≠ 0 := by
          nlinarith
        have hb' : b ≠ 0 := by
          linarith
        field_simp [hc', hb']
        <;> ring
      rw [h8]
      have h9 : c * b > 0 := by
        apply mul_pos_of_neg_of_neg
        all_goals nlinarith
        all_goals linarith
      have h10 : (a + b) * b - (a + c) * c = a * (b - c) + (b - c) * (b + c) := by
        nlinarith
      rw [h10]
      have h11 : b - c > 0 := by
        linarith
      have h12 : a * (b - c) + (b - c) * (b + c) > 0 := by
        have h13 : b - c > 0 := by
          linarith
        have h14 : a > 0 := ha
        nlinarith [show b + c < a by nlinarith [show a > 0 from ha, show b < 0 from hb, show c < 0 by nlinarith]]
      apply div_pos
      linarith
      all_goals nlinarith
    nlinarith
    all_goals nlinarith