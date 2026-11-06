import Mathlib

theorem algebra_14567 :
    {k | ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = 0 ∧
    a^2 * b^2 / ((a^2 - b * c) * (b^2 - a * c)) +
    a^2 * c^2 / ((a^2 - b * c) * (c^2 - a * b)) +
    b^2 * c^2 / ((b^2 - a * c) * (c^2 - a * b)) = k} = {1} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume k is in the set, prove k = 1.
    rintro ⟨a, b, c, ha, hb, hc, h1, heq⟩
    have h2 : a + b + c = 0 := h1
    have h3 : c = -a - b := by linarith
    have eq1 : a ^ 2 * b ^ 2 / ((a ^ 2 - b * c) * (b^2 - a * c)) + 
        a ^ 2 * c ^ 2 / ((a ^ 2 - b * c) * (c ^ 2 - a * b)) + 
        b ^ 2 * c ^ 2 / ((b^2 - a * c) * (c ^ 2 - a * b)) = 1 := by
      rw [show c = -a - b by linarith]
      have ha1 : a ≠ 0 := ha
      have hb1 : b ≠ 0 := hb
      have hc1 : (-a - b) ≠ 0 := by
        intro h
        apply hc
        linarith
      have h4 : a ^ 2 - b * (-a - b) ≠ 0 := by
        intro h'
        have h' : a ^ 2 + b * a + b ^ 2 = 0 := by nlinarith 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b), sq_nonneg (a - b)]
      have h5 : b ^ 2 - a * (-a - b) ≠ 0 := by
        intro h'
        have h' : a ^ 2 + b * a + b ^ 2 = 0 := by nlinarith 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b), sq_nonneg (a - b)]
      have h6 : (-a - b) ^ 2 - a * b ≠ 0 := by
        intro h
        have h' : a ^ 2 + b ^ 2 + a * b = 0 := by nlinarith 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b), sq_nonneg (a - b)]
      have h7 : a^2 - b * (-a - b) = a^2 + b * a + b^2 := by ring
      have h8 : b^2 - a * (-a - b) = a^2 + b * a + b^2 := by ring
      have h9 : (-a - b) ^ 2 - a * b = a^2 + b^2 + a * b := by
        nlinarith
      rw [h7, h8, h9]
      field_simp [(show a ^ 2 + b * a + b ^ 2 ≠ 0 by 
        by_contra h
        have h11 : a ^ 2 + b * a + b ^ 2 = 0 := by linarith
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b), sq_nonneg (a - b)]
      ), (show a ^ 2 + b * a + b ^ 2 ≠ 0 by 
        by_contra h
        have h11 : a ^ 2 + b * a + b ^ 2 = 0 := by linarith
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b), sq_nonneg (a - b)]
      ), (show a ^ 2 + b ^ 2 + a * b ≠ 0 by 
        by_contra h
        have h11 : a ^ 2 + b ^ 2 + a * b = 0 := by linarith 
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b), sq_nonneg (a - b)]
      ), ha, hb, mul_ne_zero ha hb]
      <;> ring
    have heq1 : k = 1 := by
      linarith [heq, eq1]
    linarith
  · -- Assume k = 1, prove that k is in the set.
    intro h
    rw [h]
    use 1, 1, -2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num