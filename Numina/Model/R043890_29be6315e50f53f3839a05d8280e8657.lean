import Mathlib

theorem algebra_260391 (a b c d : ℝ) (f : ℝ → ℝ)
    (hf : f = fun x => x^4 + a * x^3 + b * x^2 + c * x + d) :
    (∃ (A B k : ℝ), ∀ (x : ℝ), f x = (x + k)^4 + A * (x + k)^2 + B) ↔ a^3 - 4 * a * b + 8 * c = 0 := by
  constructor
  · -- Assume ∃ (A B k : ℝ), ∀ (x : ℝ), f x = (x + k)^4 + A * (x + k)^2 + B, prove a^3 - 4 * a * b + 8 * c = 0
    rintro ⟨A, B, k, heq⟩
    have eq₁ := heq 0
    have eq₂ := heq 1
    have eq₃ := heq 2
    have eq₄ := heq 3
    have eq₅ := heq 4
    simp [hf] at eq₁ eq₂ eq₃ eq₄ eq₅ 
    have eq6 : a = 4 * k := by
      linarith
    have eq7 : A = b - 6 * k ^ 2 := by
      ring_nf at eq₁ eq₂ 
      nlinarith [eq6]
    have eq8 : 4 * k ^ 3 + 2 * k * A = c := by
      ring_nf at eq₂ eq₃
      nlinarith [eq6, eq7]
    have eq9 : a ^ 3 - 4 * a * b + 8 * c = 0 := by
      have eqk : k = a / 4 := by
        linarith 
      rw [eqk] at eq7 eq8 
      nlinarith [eqk, eq7, eq8]
    linarith 
  · -- Assume a^3 - 4 * a * b + 8 * c = 0, prove ∃ (A B k : ℝ), ∀ (x : ℝ), f x = (x + k)^4 + A * (x + k)^2 + B
    intro h
    use b - 3 / 8 * a ^ 2
    use d - ((a / 4) ^ 4 + (b - 3 / 8 * a ^ 2) * (a / 4) ^ 2)
    use a / 4
    intro x
    simp [hf]
    ring_nf
    nlinarith [h, sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x * 1)]