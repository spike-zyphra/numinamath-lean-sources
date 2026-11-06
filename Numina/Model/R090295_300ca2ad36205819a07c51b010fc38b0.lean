import Mathlib

theorem algebra_306593 {a b c d : ℤ} (ha : Even a) (hb : Even b) (hc : Even c) (hd : Even d)
    (hord : 0 < a ∧ a < b ∧ b < c ∧ c < d) (hdiff : d - a = 90) (hseq1 : ∃ d, b = a + d ∧ c = b + d)
    (hseq2 : ∃ r, c = b * r ∧ d = c * r) :
    a + b + c + d = 194 := by
  rcases hseq1 with ⟨h, hb1, hc1⟩
  rcases hseq2 with ⟨r, hcr, hdr⟩
  rcases hord with ⟨ha_pos, h1, h2, h3⟩
  have h1' : b = a + h := by linarith
  have h2' : c = a + 2 * h := by linarith [hc1, h1']
  rw [hcr] at hdr
  have eq1 : a + 2 * h = (a + h) * r := by
    nlinarith [h2', h1']
  have eq2 : (a + 2 * h) * r - a = 90 := by
    nlinarith [hdr, hdiff, h2']
  have hr_lower : r > 1 := by
    nlinarith [h3, hdr, h2']
  have h4 : h * (3 * r - 2) = 90 := by
    nlinarith [eq1, eq2]
  have hr_max : r ≤ 30 := by 
    nlinarith [h4, show r > 0 by nlinarith [hr_lower]]
  have hr_min : r > 1 := by
    linarith [hr_lower]
  have hh1 : h ≤ 90 := by
    nlinarith [h4, show 3 * r - 2 > 1 by nlinarith [hr_lower]]
  have hh2 : h > 0 := by
    nlinarith [h4, show 3 * r - 2 > 1 by nlinarith [hr_lower]]
  interval_cases r <;> omega