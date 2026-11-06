import Mathlib

theorem algebra_126817 (p q a b c : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hne : p ≠ q)
    (hge : ∃ r, a = p * r ∧ q = a * r) (har : ∃ d, b = p + d ∧ c = b + d ∧ q = c + d) :
    ¬∃ x : ℝ, b * x ^ 2 - 2 * a * x + c = 0 := by
  rcases hge with ⟨r, ha1, hq1⟩
  have h1 : a ^ 2 = p * q := by
    rw [show a = p * r by linarith [ha1]]
    have h2 : q = (p * r) * r := by
      nlinarith [ha1, hq1]
    rw [show q = (p * r) * r by linarith [h2]]
    <;> nlinarith
    all_goals nlinarith
  rcases har with ⟨d, hb1, hc1, hq2⟩
  have h2 : d = (q - p) / 3 := by
    nlinarith [hb1, hc1, hq2]
  have h3 : b = (2 * p + q) / 3 := by
    nlinarith [hb1, h2]
  have h4 : c = (p + 2 * q) / 3 := by
    nlinarith [hc1, h3, h2]
  have h5 : a ^ 2 < b * c := by
    rw [h1]
    rw [h3, h4]
    nlinarith [sq_pos_of_ne_zero (show (p - q) ≠ 0 by
      by_contra h'
      apply hne
      linarith [h']
    ), mul_pos hp hq
    ]
  intro h
  rcases h with ⟨x, hx⟩
  nlinarith [sq_nonneg (b * x - a), sq_nonneg (x), sq_nonneg (b - a), sq_nonneg (c - b), sq_nonneg (x - a/b), sq_nonneg (b - c), sq_nonneg (p - q), mul_pos hp hq, mul_pos ha hp, mul_pos ha hq, mul_pos hb hc
  ]