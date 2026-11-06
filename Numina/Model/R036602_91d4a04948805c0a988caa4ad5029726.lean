import Mathlib

open Real

theorem algebra_259852 {a b c N : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hc : 0 < c ∧ c ≠ 1) (hN : 0 < N) (hge : ∃ r, b = a * r ∧ c = b * r)
    (hge' : b ^ 2 = a * c) (h1 : N ≠ 1) :
    1 / logb a N - 2 / logb b N + 1 / logb c N = 0 := by 
  have h2 : logb a N = log N / log a := by 
    field_simp [logb]

  have h3 : logb b N = log N / log b := by 
    field_simp [logb]

  have h4 : logb c N = log N / log c := by 
    field_simp [logb]

  rw [h2, h3, h4]

  have h5 : log N ≠ 0 := by 
    have hn1 : N > 0 := hN
    have hn2 : N ≠ 1 := h1
    exact log_ne_zero_of_pos_of_ne_one hn1 hn2

  have h6 : log a + log c = 2 * log b := by 
    have h7 : b ^ 2 = a * c := hge'
    have h8 : log (b ^ 2) = log (a * c) := by 
      rw [h7]

    have h9 : log (b ^ 2) = 2 * log b := by 
      simp [log_pow]

    have h10 : log (a * c) = log a + log c := by 
      rw [log_mul (by linarith [ha.left, hc.left]) (by linarith [ha.left, hc.left])]

    linarith [h8, h9, h10]

  have h7 : 1 / (log N / log a) - 2 / (log N / log b) + 1 / (log N / log c) = 
          (log a - 2 * log b + log c) / log N := by 
    field_simp [(show log N ≠ 0 by exact h5), 
      show log a ≠ 0 by 
        have h8 : a > 0 := ha.left
        have h9 : a ≠ 1 := ha.right
        exact log_ne_zero_of_pos_of_ne_one h8 h9
      , show log b ≠ 0 by 
        have h8 : b > 0 := hb.left
        have h9 : b ≠ 1 := hb.right
        exact log_ne_zero_of_pos_of_ne_one h8 h9
      , show log c ≠ 0 by 
        have h8 : c > 0 := hc.left
        have h9 : c ≠ 1 := hc.right
        exact log_ne_zero_of_pos_of_ne_one h8 h9
    ]

  have h8 : (log a - 2 * log b + log c) / log N = 0 := by 
    have h9 : log a - 2 * log b + log c = 0 := by 
        linarith

    have hne : log N ≠ 0 := h5
    field_simp [hne] at *
    <;> linarith [h9]

  linarith [h7, h8]