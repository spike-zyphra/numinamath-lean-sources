import Mathlib

theorem algebra_166336 {a b c : ℕ} (ha : a > b) (hb : b > c) (hc : a = c + 6)
    (havg : b = (a + c) / 2) (hprod : a * b * c = 46332) :
    a = 39 := by
  have h1 : a = c + 6 := hc
  have h2 : b = c + 3 := by
    rw [h1] at havg
    omega
  rw [h1, h2] at hprod
  have h3 : c ≤ 39 := by
    by_contra h
    push_neg at h
    have h4 : c ≥ 40 := by omega
    have h5 : (c + 6) * (c + 3) * c ≥ 40 * 43 * 46 := by
      have h7 : c ≥ 40 := by omega
      have h8 : c + 6 ≥ 46 := by omega
      have h9 : c + 3 ≥ 43 := by omega
      have h10 : (c + 6) * (c + 3) * c ≥ 40 * 43 * 46 := by
        have h7' : c ≥ 40 := by omega
        have h8' : c + 6 ≥ 46 := by omega
        have h9' : c + 3 ≥ 43 := by omega
        have h11 : (c + 6) * (c + 3) ≥ 46 * 43 := by
          nlinarith
        have h12 : (c + 6) * (c + 3) * c ≥ (46 * 43) * 40 := by
          have h13 : c ≥ 40 := by omega
          nlinarith [show (c + 6) * (c + 3) ≥ 46 * 43 by nlinarith, h13]
        omega
      omega
    nlinarith
  interval_cases c <;> omega