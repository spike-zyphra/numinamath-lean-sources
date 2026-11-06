import Mathlib

theorem number_theory_287913 {a b : ℕ → ℝ} (ha : ∀ n, a n = (2 + Real.sqrt 7) ^ (2 * n + 1))
    (hb : ∀ n, b n = a n - ⌊a n⌋) :
    ∀ n, Odd (a n * b n) := by
  intro n
  have h1 : a n = (2 + Real.sqrt 7) ^ (2 * n + 1) := ha n
  have h2 : b n = a n - ⌊a n⌋ := hb n
  have h3 : Odd (a n * b n) := by
    rw [h2, h1]
    use (( (2 + Real.sqrt 7) ^ (2 * n + 1) * ( (2 + Real.sqrt 7) ^ (2 * n + 1) - (⌊(2 + Real.sqrt 7) ^ (2 * n + 1)⌋ : ℝ)) ) - 1 ) / 2
    field_simp
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> nlinarith [ Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), show 1 < Real.sqrt 7 by nlinarith [ Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num) ] ]
  simpa using h3