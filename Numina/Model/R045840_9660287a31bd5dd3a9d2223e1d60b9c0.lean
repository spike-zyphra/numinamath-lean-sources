import Mathlib

theorem algebra_277763 (a b c : ℕ) (ha : a = 90) (hb : b = 98) (hc : c = 2 * m)
    (h : a * 88 + b * 98 + c * 4 * m = 5 * k) (hk : 8000 < k ∧ k < 9000) :
    m = 36 := by 
  rw [ha] at h
  rw [hb] at h
  rw [hc] at h
  have hk1 : k > 8000 := by linarith [hk.1]
  have hk2 : k < 9000 := by linarith [hk.2]
  have h1 : 90 * 88 + 98 * 98 + (2 * m) * 4 * m = 5 * k := by
    nlinarith
  have h2 : m ≤ 58 := by
    nlinarith
  have h3 : m ≥ 54 := by
    nlinarith
  interval_cases m <;> omega