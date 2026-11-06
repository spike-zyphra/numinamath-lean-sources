import Mathlib

theorem algebra_260737_1 {x : ℝ} (hx : x ≠ 0) (hx' : 8*x+3 ≠ 0) (hx'': 7*x-3 ≠ 0)
  : 2 + 5 / (4 * x) - 15 / (4 * x * (8 * x + 3)) = (2 * (7 * x + 1)) / (7 * x - 3) ↔ x = 9 := by
  constructor <;> rintro h
  . -- multiply all denominators and normalize to get a cubic equation
    field_simp at h
    ring_nf at h
    replace h : 96 * x^2 * (x - 9) = 0 := by linear_combination h
    -- due to x ≠ 0, we get x = 9 = 0
    simp [hx] at h
    linarith
    -- 9 is a root, prove by pluggin in
  . rw [h]
    norm_num

theorem algebra_260737_2 {x : ℝ} (hx : x ≠ 0)
  : 2 / x + 1 / x ^ 2 - (7 + 10 * x) / (x ^ 2 * (x ^ 2 + 7)) = 2 / (x + 3 / (x + 4 / x)) ↔ x = 4 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    -- simplify the right side.
    have h1 : x + 4 / x = (x ^ 2 + 4) / x := by field_simp; ring
    have h2 : (2 / (x + 3 / (x + 4 / x))) = 2 * (x ^ 2 + 4) / (x ^ 3 + 7 * x) := by
      rw [show x + 3 / (x + 4 / x) = (x ^ 3 + 7 * x) / (x ^ 2 + 4) by
        rw [show x + 4 / x = (x ^ 2 + 4) / x by field_simp; ring]
        field_simp
        <;> ring
        <;> field_simp
        <;> ring
      ]
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h2] at h
    have hx2_ne : x ^ 2 ≠ 0 := by
      intro h1
      have : x = 0 := by
        nlinarith
      contradiction
    have hx2_add4_ne : x ^ 2 + 4 ≠ 0 := by
      by_contra h1
      have h1' : x ^ 2 = -4 := by nlinarith
      have h2 : x ^ 2 ≥ 0 := sq_nonneg x
      nlinarith
    have h3 : x ^ 3 + 7 * x ≠ 0 := by
      by_contra h1
      have h4 : x * (x ^ 2 + 7) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- x = 0 is impossible
        exfalso
        exact hx h5
      · -- x ^ 2 + 7 = 0 is impossible
        have : x ^ 2 = -7 := by nlinarith
        have h2 : x ^ 2 ≥ 0 := sq_nonneg x
        nlinarith
    field_simp at h
    ring_nf at h
    -- now `h` is a polynomial equation
    -- convert polynomial equation into factors 
    have h_zero : x ^ 5 * (x - 4) * (x ^ 2 + 7) = 0 := by
      nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (x ^ 2 + 4), sq_nonneg (x ^ 3 + 7 * x),
        sq_nonneg (x ^ 2 - 16), sq_nonneg (x ^ 2 + 7), sq_nonneg (x - 4), sq_nonneg (x + 4)]
    cases' (mul_eq_zero.mp h_zero) with h1 h2
    · cases' (mul_eq_zero.mp h1) with h4 h5
      · -- we get x ^ 5 = 0 => x = 0 is impossible
        have h_zero_5 : x ^ 5 = 0 := by
          nlinarith
        have hx'1 : x = 0 := by
          have : x ^ 5 = 0 := h_zero_5
          simp at this
          linarith
        contradiction
      · -- we get x - 4 = 0 => x = 4
        linarith
    · -- we get x ^ 2 + 7 = 0 => impossible
      have h_zero_s2 : x ^ 2 + 7 = 0 := by
        nlinarith
      -- is_zero_s2 : x^2 = -7
      have hx'2 : x ^ 2 = -7 := by
        nlinarith
      -- contradicts by x^2 >= 0
      have hx'2_neg : x ^ 2 + 7 = 0 := h_zero_s2
      have h_non_pos : x ^ 2 >= 0 := sq_nonneg x
      nlinarith
  · -- Assume right side, prove left side
    intro h
    rw [h]
    norm_num
    <;> field_simp
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> field_simp
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> field_simp
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> field_simp
    <;> norm_num