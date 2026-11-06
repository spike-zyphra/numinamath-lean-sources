import Mathlib


open BigOperators Real Set


theorem algebra_223937 :
  IsGreatest {x | ∃ a b c : ℝ, a ∈ Ioc 0 1 ∧ b ∈ Ioc 0 1 ∧ c ∈ Ioc 0 1 ∧
    x = (sqrt (8 * a^4 + b) + sqrt (8 * b^4 + c) + sqrt (8 * c^4 + a) - 3) / (a + b + c)} 2 := by

  constructor
  · -- Show 2 is in the set
    use 1, 1, 1
    constructor
    · -- Show a ∈ Ioc 0 1
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show b ∈ Ioc 0 1
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show c ∈ Ioc 0 1
      exact ⟨by norm_num, by norm_num⟩
    · -- Show 2 = (sqrt(8 * 1^4 + 1) + sqrt(8 * 1^4 + 1) + sqrt(8 * 1^4 + 1) - 3) / (1 + 1 + 1)
      have h1 : sqrt (8 * (1 : ℝ) ^ 4 + (1 : ℝ)) = 3 := by
        rw [show (8 * (1 : ℝ) ^ 4 + (1 : ℝ) ) = (9 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num
  · -- Show 2 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hx_eq⟩

    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩

    have lemma_1 (x y : ℝ) (hx : 0 < x ∧ x ≤ 1) (hy : 0 < y ∧ y ≤ 1) :
        Real.sqrt (8 * x ^ 4 + y) ≤ 2 * x + 1 := by
      have h1 : 0 < x := hx.1
      have h2 : x ≤ 1 := hx.2
      have h3 : 0 < y := hy.1
      have h4 : y ≤ 1 := hy.2
      have h5 : 0 ≤ (2 * x + 1 : ℝ) := by nlinarith
      have h6 : (8 * x ^ 4 + y : ℝ) ≤ (2 * x + 1) ^ 2 := by
        nlinarith [sq_nonneg (x ^ 2 - x / 2 ), sq_nonneg (x - 1 / 2 ), sq_nonneg (x ^ 2 - 1 / 2 ), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1 / 2) * (x - 1 / 2) ), sq_nonneg (2 * x ^ 2 - 1 ), mul_pos h1 (show 0 < (1 - x + x : ℝ) by nlinarith), mul_nonneg (show 0 ≤ (1 - x) by linarith) (show 0 ≤ (2 * x ^ 2 + 2 * x + 1 : ℝ) by nlinarith)]
      have h7 : Real.sqrt (8 * x ^ 4 + y) ≤ (2 * x + 1 : ℝ) := by
        have hx8_pos : 0 ≤ (8 * x ^ 4 + y : ℝ) := by
          have hx_pos : x > 0 := h1
          have hy_pos : y > 0 := h3
          positivity
        have h88 : (Real.sqrt (8 * x ^ 4 + y) : ℝ) ^ 2 = (8 * x ^ 4 + y : ℝ) := by
          rw [Real.sq_sqrt (by positivity)]
        have h99 : (2 * x + 1 : ℝ) ^ 2 = 4 * x ^ 2 + 4 * x + 1 := by
          ring_nf
        have h100 : (8 * x ^ 4 + y : ℝ) ≤ (4 * x ^ 2 + 4 * x + 1 : ℝ) := by
          nlinarith
        have h11 : (Real.sqrt (8 * x ^ 4 + y) : ℝ) ^ 2 ≤ (2 * x + 1) ^ 2 := by
          nlinarith
        have h12 : (Real.sqrt (8 * x ^ 4 + y) : ℝ) ≥ 0 := Real.sqrt_nonneg (8 * x ^ 4 + y)
        have h13 : (2 * x + 1 : ℝ) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (8 * x ^ 4 + y), sq_nonneg (Real.sqrt (8 * x ^ 4 + y) - (2 * x + 1 : ℝ))]
      linarith

    have h1 : Real.sqrt (8 * a ^ 4 + b) ≤ 2 * a + 1 := by
      have hx1 : 0 < a := ha1
      have hx2 : a ≤ 1 := ha2
      have hy1 : 0 < b := hb1
      have hy2 : b ≤ 1 := hb2
      have h0 : 0 < a ∧ a ≤ 1 := ⟨ha1, ha2⟩
      have h10 : 0 < b ∧ b ≤ 1 := ⟨hb1, hb2⟩
      apply lemma_1 a b h0 h10

    have h2 : Real.sqrt (8 * b ^ 4 + c) ≤ 2 * b + 1 := by
      have hx1 : 0 < b := hb1
      have hx2 : b ≤ 1 := hb2
      have hy1 : 0 < c := hc1
      have hy2 : c ≤ 1 := hc2
      have h0 : 0 < b ∧ b ≤ 1 := ⟨hb1, hb2⟩
      have h10 : 0 < c ∧ c ≤ 1 := ⟨hc1, hc2⟩
      apply lemma_1 b c h0 h10

    have h3 : Real.sqrt (8 * c ^ 4 + a) ≤ 2 * c + 1 := by
      have hx1 : 0 < c := hc1
      have hx2 : c ≤ 1 := hc2
      have hy1 : 0 < a := ha1
      have hy2 : a ≤ 1 := ha2
      have h0 : 0 < c ∧ c ≤ 1 := ⟨hc1, hc2⟩
      have h10 : 0 < a ∧ a ≤ 1 := ⟨ha1, ha2⟩
      apply lemma_1 c a h0 h10

    have h4 : Real.sqrt (8 * a^4 + b) + Real.sqrt (8 * b^4 + c) + Real.sqrt (8 * c^4 + a) - 3 ≤ 2 * (a + b + c) := by
      have h8 : Real.sqrt (8 * a^4 + b) ≤ 2 * a + 1 := h1
      have h9 : Real.sqrt (8 * b^4 + c) ≤ 2 * b + 1 := h2
      have h10 : Real.sqrt (8 * c^4 + a) ≤ 2 * c + 1 := h3
      linarith

    have h6 : (Real.sqrt (8 * a^4 + b) + Real.sqrt (8 * b^4 + c) + Real.sqrt (8 * c^4 + a) - 3) / (a + b + c) ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith

    linarith [hx_eq, h6]