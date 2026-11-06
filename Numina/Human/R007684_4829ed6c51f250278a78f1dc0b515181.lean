import Mathlib

/- Homewood Middle School has 1200 students, and 730 of these students attend a summer picnic. If two-thirds of the girls in the school and one-half of the boys in the school attend the picnic, how many girls attend the picnic?  (Assume that each student in the school is either a boy or a girl.) -/
theorem algebra_12921 {g b : ℕ} (hg : g + b = 1200) (hb : g ≠ 0) (hgp : (2 / 3 : ℚ) * g + (1 / 2 : ℚ) * b = 730) :
    (2 / 3 : ℚ) * g = 520 := by
  field_simp at hgp ⊢
  ring_nf at hgp ⊢
  norm_cast at hgp ⊢
  linarith