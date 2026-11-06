import Mathlib

theorem algebra_325885 {f : ℝ → ℝ} (h : ∀ x, f (x + 5) = -f x)
    (hf : ∀ x ∈ Set.Ioo 5 10, f x = 1 / x) :
    f 2003 = -1 / 8 := by

  have h1 : ∀ (n : ℕ), f (8 + (↑n : ℝ) * 5) = (-1 : ℝ) ^ n * (f 8) := by
    intro n 
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have eq2 : f (8 + ((↑(n + 1 : ℕ) : ℝ)) * 5) = f ((8 + (↑n * 5 : ℝ)) + 5) := by
        simp at *
        <;> ring_nf 
      rw [eq2]
      have eq3 : f ((8 + (↑n * 5 : ℝ)) + 5) = - f (8 + (↑n * 5 : ℝ)) := by
        specialize h (8 + (↑n * 5 : ℝ))
        simpa using h
      rw [eq3, ih]
      ring_nf 
  have h2 : f 8 = 1 / (8 : ℝ) := by
    apply hf
    constructor
    norm_num 
    norm_num
  have h3 : f 2003 = (-1 : ℝ) ^ 399 * (f 8) := by
    specialize h1 399
    norm_num at h1 ⊢ 
    linarith 
  rw [h2] at h3 
  have h4 : (-1 : ℝ) ^ 399 = -1 := by
    norm_num
  rw [h4] at h3 
  linarith