import Mathlib

theorem algebra_224343 {a b : ℝ} (ha : a ≠ 2016) (hb : b ≠ 2016)
    (h1 : ∃ r, 2016 = a * r ∧ b = 2016 * r) (h2 : ∃ d, (a + 2016) = b + d ∧ (b + d) = a + b) :
    a = -1008 ∧ b = -4032 := by
  rcases h1 with ⟨r, h11, h12⟩
  rcases h2 with ⟨d, h21, h22⟩
  have h3 : d = a := by
    linarith
  have h4 : a + 2016 = b + a := by
    rw [show d = a by linarith [h3]] at h21
    linarith
  have h5 : b = 2016 := by
    linarith
  contradiction