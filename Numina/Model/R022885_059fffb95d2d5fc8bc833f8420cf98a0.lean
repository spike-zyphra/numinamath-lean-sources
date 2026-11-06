import Mathlib

theorem algebra_303275 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc (-1) 1, 0 ≤ f x ∧ f x ≤ 1)
    (hf1 : ∀ x, f x = a * x - b) :
    -4 / 5 ≤ (3 * a + b + 1) / (a + 2 * b - 2) ∧ (3 * a + b + 1) / (a + 2 * b - 2) ≤ 2 / 7 := by
  have h1 := hf 1 (by norm_num)
  rw [hf1] at h1
  have h2 := hf (-1) (by norm_num)
  rw [hf1] at h2
  have h3 := hf 0 (by norm_num)
  rw [hf1] at h3
  have h4 : 0 ≤ a - b := by linarith
  have h5 : a - b ≤ 1 := by linarith
  have h6 : 0 ≤ -a - b := by linarith
  have h7 : -a - b ≤ 1 := by linarith
  have h8 : 0 ≤ -b := by linarith
  have h9 : -b ≤ 1 := by linarith
  have h10 : a + 2 * b - 2 < 0 := by
    nlinarith
  have h11 : -4 / 5 ≤ (3 * a + b + 1) / (a + 2 * b - 2) := by
    apply (le_div_iff_of_neg' h10).mpr
    nlinarith
  have h12 : (3 * a + b + 1) / (a + 2 * b - 2) ≤ 2 / 7 := by
    apply (div_le_iff_of_neg' h10).mpr
    nlinarith
  constructor <;> try linarith