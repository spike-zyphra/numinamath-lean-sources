import Mathlib

theorem algebra_292836 {p : ℝ} (hp : ∃ x y, x ≠ y ∧ x^2 + p * x - 6 = 0 ∧ y^2 + p * y - 6 = 0 ∧
    abs x + abs y = 5) :
    p = 1 ∨ p = -1 := by
  rcases hp with ⟨x, y, hxy, hx, hy, habs⟩
  have h1 : x ^ 2 + p * x - 6 = 0 := hx
  have h2 : y ^ 2 + p * y - 6 = 0 := hy
  have h3 : x ^ 2 + p * x - 6 - (y ^ 2 + p * y - 6) = 0 := by linarith [hx, hy]
  have h4 : (x - y) * (x + y + p) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- x - y = 0, but x ≠ y, contradiction
    exfalso
    apply hxy
    linarith
  · -- x + y + p = 0, so x + y = -p
    have hsum : x + y = -p := by linarith
    by_cases h5 : x ≥ 0
    · -- x ≥ 0
      by_cases h6 : y ≥ 0
      · -- y ≥ 0
        rw [abs_of_nonneg h5, abs_of_nonneg h6] at habs
        -- x + y = 5, but x + y = -p
        -- x + y = 5 means p = -5
        -- The equation becomes x^2 - 5x - 6 = 0
        -- The roots of x^2 - 5x - 6 = 0 are x = 6 and x = -1
        -- since both ≥0, impossible
        nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h; apply hxy; linarith)]
      · -- y < 0
        rw [abs_of_nonneg h5, abs_of_neg (not_le.mp h6)] at habs
        have h1' : (p - 1) * (p + 1) = 0 := by
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h; apply hxy; linarith)]
        cases' (mul_eq_zero.mp h1') with hp1 hp2
        · -- p = 1
          left
          linarith
        · -- p = -1
          right
          linarith
    · -- x < 0
      by_cases h6 : y ≥ 0
      · -- y ≥ 0
        rw [abs_of_neg (not_le.mp h5), abs_of_nonneg h6] at habs
        have h1' : (p - 1) * (p + 1) = 0 := by
          nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h; apply hxy; linarith)]
        cases' (mul_eq_zero.mp h1') with hp1 hp2
        · -- p = 1
          left
          linarith
        · -- p = -1
          right
          linarith
      · -- y < 0
        rw [abs_of_neg (not_le.mp h5), abs_of_neg (not_le.mp h6)] at habs
        -- (|x| + |y| = -x - y = 5) and (x + y = -p) implies (x + y) = -5 => p = 5
        -- The equation becomes z^2 +5z -6 =0, roots -6 and 1
        -- require both <0, impossible.
        nlinarith [sq_pos_of_ne_zero (show (x - y) ≠ 0 by intro h; apply hxy; linarith)]