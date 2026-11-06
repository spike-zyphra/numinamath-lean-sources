import Mathlib

theorem algebra_13837 :
    IsLeast {n : ℤ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ n = ⌊(a + b) / c⌋ + ⌊(b + c) / a⌋ + ⌊(c + a) / b⌋} 4 := by
  constructor
  · -- Show 4 is in the set
    use 1, 1, 0.7
    constructor
    · norm_num -- 1 > 0
    constructor
    · norm_num -- 1 > 0
    constructor
    · norm_num -- 0.7 > 0
    norm_num [Int.floor_eq_iff]
  · -- Show 4 is minimal
    intro n hn
    rcases hn with ⟨a, b, c, ha, hb, hc, hn⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 3 := by omega
    have h2 : n = ⌊(a + b) / c⌋ + ⌊(b + c) / a⌋ + ⌊(c + a) / b⌋ := by
      linarith [hn]
    have h7 : ⌊(a + b) / c⌋ + ⌊(b + c) / a⌋ + ⌊(c + a) / b⌋ ≥ 4 := by
      have h1 : ⌊(a + b) / c⌋ > ((a + b) / c) - 1 := by
        have h5 : ⌊(a + b) / c⌋ ≤ (a + b) / c := by 
          exact Int.floor_le ((a + b) / c)
        have h8 : (a + b) / c < (⌊(a + b) / c⌋ : ℝ) + 1 := by 
          exact Int.lt_floor_add_one ((a + b) / c)
        linarith
      have h2 : ⌊(b + c) / a⌋ > ((b + c) / a) - 1 := by
        have h5 : ⌊(b + c) / a⌋ ≤ (b + c) / a := by 
          exact Int.floor_le ((b + c) / a)
        have h8 : (b + c) / a < (⌊(b + c) / a⌋ : ℝ) + 1 := by 
          exact Int.lt_floor_add_one ((b + c) / a)
        linarith
      have h3 : ⌊(c + a) / b⌋ > ((c + a) / b) - 1 := by
        have h5 : ⌊(c + a) / b⌋ ≤ (c + a) / b := by 
          exact Int.floor_le ((c + a) / b)
        have h8 : (c + a) / b < (⌊(c + a) / b⌋ : ℝ) + 1 := by 
          exact Int.lt_floor_add_one ((c + a) / b)
        linarith
      have h4 : (a + b) / c + (b + c) / (a) + (c + a) / (b) ≥ 6 := by
        have h1' : (a + b) / c + (b + c) / (a) + (c + a) / (b) - 6 ≥ 0 := by
          have h11 : (a + b) / c + (b + c) / (a) + (c + a) / (b) - 6 =
            ( (a + b)*a*b + (b + c)*c*b + (c + a)*c*a - 6*a*b*c ) / (a*b*c) := by
            field_simp
            ring
          rw [h11]
          have h12 : a * b * c > 0 := by positivity
          have h13 : (a + b)*a*b + (b + c)*c*b + (c + a)*c*a - 6*a*b*c ≥ 0 := by
            nlinarith [sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*a), sq_nonneg (c*a - a*b), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc ]
          have h14 : ( (a + b)*a*b + (b + c)*c*b + (c + a)*c*a - 6*a*b*c ) / (a*b*c) ≥ 0 := by
            apply div_nonneg
            linarith
            positivity
          linarith
        nlinarith
      have h7 : (⌊(a + b) / c⌋ : ℝ) + (⌊(b + c) / a⌋ : ℝ) + (⌊(c + a) / b⌋ : ℝ) > 3 := by
        have h8 : (⌊(a + b) / c⌋ : ℝ) + (⌊(b + c) / a⌋ : ℝ) + (⌊(c + a) / b⌋ : ℝ) > ((a + b) / c) - 1 + ((b + c) / a) - 1 + ((c + a) / b) - 1 := by
          linarith
        have h9 : ((a + b) / c) - 1 + ((b + c) / a) - 1 + ((c + a) / b) - 1 = (a + b) / c + (b + c) / a + (c + a) / b - 3 := by 
          ring
        have h10 : (a + b) / c + (b + c) / a + (c + a) / b - 3 ≥ 3 := by
          linarith
        nlinarith
      have h8 : ⌊(a + b) / c⌋ + ⌊(b + c) / a⌋ + ⌊(c + a) / b⌋ ≥ 4 := by
        by_contra h
        push_neg at h
        have h9 : ⌊(a + b) / c⌋ + ⌊(b + c) / a⌋ + ⌊(c + a) / b⌋ ≤ 3 := by omega
        have h10 : (⌊(a + b) / c⌋ : ℝ) + (⌊(b + c) / a⌋ : ℝ) + (⌊(c + a) / b⌋ : ℝ) ≤ (3 : ℝ) := by
          exact_mod_cast h9
        linarith
      linarith
    omega