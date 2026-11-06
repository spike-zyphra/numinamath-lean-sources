import Mathlib


open Real


theorem algebra_96747 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
(hd : d ≠ 0) (f : ℝ → ℝ) (hf : ∀ x , (c * x + d ≠ 0) →  f x = (a * x + b) / (c * x + d))
(h19 : (c * 19 + d ≠ 0) ∧ f 19 = 19) (h97 : (c * 97 + d ≠ 0) ∧ f 97 = 97) (hff : ∀ x, (c * x + d ≠ 0) → (c * (f x) + d ≠ 0) ∧ f (f x) = x) :
a / c = 58 := by

  rcases h19 with ⟨h19ne, h19f⟩
  have eq1 : a * 19 + b = 19 * (c * 19 + d) := by
    have h191 : f 19 = (a * 19 + b) / (c * 19 + d) := by
      apply hf 19
      exact h19ne
    rw [h191] at h19f
    field_simp [h19ne] at h19f
    linarith

  rcases h97 with ⟨h97ne, h97f⟩
  have eq2 : a * 97 + b = 97 * (c * 97 + d) := by
    have h971 : f 97 = (a * 97 + b) / (c * 97 + d) := by
      apply hf 97
      exact h97ne
    rw [h971] at h97f
    field_simp [h97ne] at h97f
    linarith

  have eq3 : 78 * a = 9048 * c + 78 * d := by
    nlinarith

  have eq4 : a = 116 * c + d := by
    linarith

  have h0 : (c * (0 : ℝ) + d ≠ 0) := by
    intro h11
    apply hd
    linarith

  have h00 : (c * (f 0) + d ≠ 0) ∧ f (f 0) = (0 : ℝ) := hff 0 h0

  have eq5 : f (f 0) = (0 : ℝ) := h00.2

  have hf0 : f 0 = (a * (0 : ℝ) + b) / (c * (0 : ℝ) + d) := by
    apply hf 0
    exact h0

  have hf00 : f 0 = b / d := by
    rw [hf0]
    field_simp [hd]

  have h1 : (c * (f 0) + d ≠ 0) := h00.1
  have hf000 : f (f 0) = (a * (f 0) + b) / (c * (f 0) + d) := by
    apply hf (f 0)
    exact h1

  rw [hf000] at eq5

  have eq6 : a * (f 0) + b = 0 := by
    field_simp [h1] at eq5
    linarith

  rw [hf00] at eq6

  have eq7 : a * b + b * d = 0 := by
    field_simp [hd] at eq6
    nlinarith

  have eq8 : b * (a + d) = 0 := by
    nlinarith

  have eq9 : a + d = 0 := by
    apply (mul_left_inj' hb).mp
    linarith

  have eq10 : d = -a := by linarith

  have eq11 : a = 58 * c := by
    rw [eq10] at eq4
    nlinarith

  have hcne : c ≠ 0 := hc
  field_simp [hcne]
  nlinarith