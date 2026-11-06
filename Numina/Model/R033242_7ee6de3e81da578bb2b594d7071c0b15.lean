import Mathlib

theorem inequalities_117037
    (a b c : ℝ)
    (ha : a ∈ Set.Icc 2 4)
    (hb : b ∈ Set.Icc 2 4)
    (hc : c ∈ Set.Icc 2 4) :
    2 / (a + b ^ 2 + c ^ 3) + 2 / (b + c ^ 2 + a ^ 3) +
    2 / (c + a ^ 2 + b ^ 3) ≤
    3 / (a + b + c)
  := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  have h1 : 2 ≤ a := by linarith
  have h2 : a ≤ 4 := by linarith
  have h3 : 2 ≤ b := by linarith
  have h4 : b ≤ 4 := by linarith
  have h5 : 2 ≤ c := by linarith
  have h6 : c ≤ 4 := by linarith
  have h7 : a ^ 3 ≥ 8 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a - 4), sq_nonneg (a + 4)]
  have h8 : b ^ 2 ≥ 4 := by
    nlinarith [sq_nonneg (b - 2), sq_nonneg (b + 2), sq_nonneg (b - 4), sq_nonneg (b + 4)]
  have h9 : c ^ 3 ≥ 8 := by
    nlinarith [sq_nonneg (c - 2), sq_nonneg (c + 2), sq_nonneg (c - 4), sq_nonneg (c + 4)]
  have h10 : a ^ 2 ≥ 4 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a - 4), sq_nonneg (a + 4)]
  have h11 : b ^ 3 ≥ 8 := by
    nlinarith [sq_nonneg (b - 2), sq_nonneg (b + 2), sq_nonneg (b - 4), sq_nonneg (b + 4)]
  have h12 : c ^ 2 ≥ 4 := by
    nlinarith [sq_nonneg (c - 2), sq_nonneg (c + 2), sq_nonneg (c - 4), sq_nonneg (c + 4)]
  have h13 : 0 < a + b ^ 2 + c ^ 3 := by
    nlinarith
  have h14 : 0 < b + c ^ 2 + a ^ 3 := by
    nlinarith
  have h15 : 0 < c + a ^ 2 + b ^ 3 := by
    nlinarith
  have h16 : 2 / (a + b ^ 2 + c ^ 3) + 2 / (b + c ^ 2 + a ^ 3) + 2 / (c + a ^ 2 + b ^ 3) ≤ 3 / (a + b + c) := by
    have h17 : 0 < a + b + c := by
      nlinarith
    have h18 : 2 * (a + b + c) ≤ a + b ^ 2 + c ^ 3 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
        sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (c - 4),
          h7, h8, h9, h10, h11, h12]
    have h19 : 2 * (a + b + c) ≤ b + c ^ 2 + a ^ 3 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
        sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (c - 4),
          h7, h8, h9, h10, h11, h12]
    have h20 : 2 * (a + b + c) ≤ c + a ^ 2 + b ^ 3 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
        sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (c - 4),
          h7, h8, h9, h10, h11, h12]
    have h21 : 2 / (a + b ^ 2 + c ^ 3) ≤ 1 / (a + b + c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h22 : 2 / (b + c ^ 2 + a ^ 3) ≤ 1 / (a + b + c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h23 : 2 / (c + a ^ 2 + b ^ 3) ≤ 1 / (a + b + c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h24 : 2 / (a + b ^ 2 + c ^ 3) + 2 / (b + c ^ 2 + a ^ 3) + 2 / (c + a ^ 2 + b ^ 3) ≤ 3 / (a + b + c) := by
      have h25 : 2 / (a + b ^ 2 + c ^ 3) + 2 / (b + c ^ 2 + a ^ 3) + 2 / (c + a ^ 2 + b ^ 3) ≤ 1 / (a + b + c) + 1 / (a + b + c) + 1 / (a + b + c) := by
        linarith [h21, h22, h23]
      have h26 : 1 / (a + b + c) + 1 / (a + b + c) + 1 / (a + b + c) = 3 / (a + b + c) := by
        ring_nf
      linarith [h25, h26]
    linarith
  linarith [h16]