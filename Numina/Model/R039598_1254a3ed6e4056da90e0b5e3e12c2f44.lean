import Mathlib

theorem algebra_9728 {l w h : ℕ} (hw : w = h + 3) (hl : l = w + 3)
    (hvol : l * w * h = 7820) :
    2 * (l * w + w * h + l * h) = 2382 := by
  have hw_eq : w = h + 3 := hw
  have hl_eq : l = w + 3 := hl
  rw [hw_eq] at hl_eq
  have hl_eq2 : l = h + 6 := by
    omega
  rw [hl_eq2, hw_eq] at hvol
  have h_eq17 : h = 17 := by
    have eq1 : h ≤ 20 := by
      by_contra h'
      push_neg at h'
      have h1 : h ≥ 21 := by omega
      have h2 : (h + 6) * (h + 3) * h ≥ 21 * 24 * 21 := by
        have h3 : h ≥ 21 := by omega
        have h4 : h + 3 ≥ 24 := by omega
        have h5 : h + 6 ≥ 27 := by omega
        have h6 : (h + 6) * (h + 3) ≥ 27 * 24 := by
          nlinarith
        nlinarith
      nlinarith
    interval_cases h <;> try { omega }
  have hw_eq20 : w = 20 := by
    calc
      w = h + 3 := by rw [hw_eq]
      _ = 17 + 3 := by rw [h_eq17]
      _ = 20 := by norm_num
  have hl_eq23 : l = 23 := by
    calc
      l = h + 6 := by rw [hl_eq2]
      _ = 17 + 6 := by rw [h_eq17]
      _ = 23 := by norm_num
  calc
    2 * (l * w + w * h + l * h) = 2 * (23 * 20 + 20 * 17 + 23 * 17) := by
      rw [hl_eq23, hw_eq20, h_eq17]
    _ = 2382 := by
      norm_num