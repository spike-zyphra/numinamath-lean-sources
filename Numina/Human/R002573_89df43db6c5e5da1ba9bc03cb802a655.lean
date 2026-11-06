import Mathlib
set_option maxHeartbeats 800000
/- If the arithmetic mean of $a$ and $b$ is double their geometric mean, with $a>b>0$, then a possible value for the ratio $a/b$, to the nearest integer, is:
$\text{(A) } 5\quad \text{(B) } 8\quad \text{(C) } 11\quad \text{(D) } 14\quad \text{(E) none of these}$ -/
theorem algebra_95644 {a b : ℝ} (ha : 0 < b) (hb : b < a) (h : (a + b) / 2 = 2 * Real.sqrt (a * b)) :
    round (a / b) = 14 := by
  -- Multiply both sides of the hypothesis by 2 to simplify
  have h1 : a + b = 4 * Real.sqrt (a * b) := by linarith

  -- Square both sides of the equation to eliminate the square root
  have h2 : (a + b) ^ 2 = 16 * (a * b) := by
    calc
      (a + b) ^ 2 = (4 * Real.sqrt (a * b)) ^ 2 := by rw [h1]
      _ = 16 * (Real.sqrt (a * b) ^ 2) := by ring
      _ = 16 * (a * b) := by
        rw [Real.sq_sqrt]
        nlinarith

  -- Expand (a + b)² and rearrange to get a quadratic equation in terms of a and b
  have h3 : a ^ 2 - 14 * a * b + b ^ 2 = 0 := by
    nlinarith [h2]

  -- Divide the quadratic equation by b² to get a quadratic in terms of a/b
  have h4 : (a / b) ^ 2 - 14 * (a / b) + 1 = 0 := by
    have hb2 : b ≠ 0 := by linarith
    field_simp
    nlinarith [h3]

  -- Solve the quadratic equation for a/b using the quadratic formula
  -- The solutions are 7 + 4√3 and 7 - 4√3
  have h5 : a / b = 7 + 4 * Real.sqrt 3 := by
    have hquadratic : (a / b) ^ 2 - 14 * (a / b) + 1 = 0 := h4
    -- Factor the quadratic equation
    have h6 : (a / b) ^ 2 - 14 * (a / b) + 1 = (a / b - (7 + 4 * Real.sqrt 3)) * (a / b - (7 - 4 * Real.sqrt 3)) := by
      ring_nf
      have h7 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [h7, Real.sqrt_nonneg 3]
    rw [h6] at hquadratic
    cases' (mul_eq_zero.mp hquadratic) with h7 h8
    · -- Case a/b = 7 + 4√3
      linarith
    · -- Case a/b = 7 - 4√3
      have h9 : a / b = 7 - 4 * Real.sqrt 3 := by linarith
      -- Show that a/b > 1 from the original conditions
      have h10 : a / b > 1 := by
        have h13 : a / b > 1 := by
          apply (lt_div_iff₀' (by linarith)).mpr
          linarith
        exact h13
      -- Show that 7 - 4√3 ≤ 1, which contradicts a/b > 1
      have h11 : 7 - 4 * Real.sqrt 3 ≤ 1 := by
        have h14 : Real.sqrt 3 ≥ 3 / 2 := by
          have h15 : (3 / 2 : ℝ) ^ 2 < (3 : ℝ) := by norm_num
          have h16 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
          by_contra h
          push_neg at h
          have h17 : Real.sqrt 3 ^ 2 < (3 / 2 : ℝ) ^ 2 := by nlinarith [h16, h]
          nlinarith [h15, h17]
        linarith
      -- Derive a contradiction, eliminating this case
      linarith [h9, h10, h11]

  -- Prove that a/b ≥ 13.5 by showing that √3 ≥ 13/8
  have h6 : 13.5 ≤ (a / b) := by
    rw [h5]
    have h7 : Real.sqrt 3 ≥ 13 / 8 := by
      have h8 : (13 / 8 : ℝ) ^ 2 < (3 : ℝ) := by norm_num
      have h9 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      by_contra h
      push_neg at h
      have h10 : Real.sqrt 3 ^ 2 < (13 / 8 : ℝ) ^ 2 := by nlinarith [h9, h]
      nlinarith [h8, h10]
    ring_nf at *
    nlinarith [h7, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  -- Prove that a/b < 14.5 by showing that √3 < 15/8
  have h7 : (a / b) < 14.5 := by
    rw [h5]
    have h8 : Real.sqrt 3 < (15 / 8 : ℝ) := by
      have h9 : Real.sqrt 3 ^ 2 < (15 / 8 : ℝ) ^ 2 := by
        have h10 : (3 : ℝ) < (15 / 8 : ℝ) ^ 2 := by norm_num
        nlinarith [h10, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith [show 0 ≤ Real.sqrt 3 by apply Real.sqrt_nonneg, h9]
    ring_nf at *
    nlinarith [h8, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  -- Apply the definition of rounding to the nearest integer
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor
  · -- Prove that 14 ≤ (a/b) + 0.5, which means a/b rounds up to at least 14
    norm_num at h6 ⊢
    linarith
  · -- Prove that (a/b) + 0.5 < 15, which means a/b rounds to at most 14
    norm_num at h7 ⊢
    linarith
