import Mathlib

theorem algebra_158405 {f : ℝ → ℝ} (h1 : ∀ x, f (1 + x) = f (3 - x)) (h2 : ∀ x, f (2 + x) = -f (1 - x)) :
    ∑ i ∈ Finset.range 100, f (i + 1) = 0 := by

  have h3 : ∀ x, f x = - f (x - 1) := by
    intro x
    have h4 : f x = f (4 - x) := by
      have h5 : f (1 + (x - 1)) = f (3 - (x - 1)) := by
        apply h1
      have h6 : 1 + (x - 1) = (x : ℝ) := by ring
      have h7 : (3 - (x - 1) : ℝ) = (4 - x : ℝ) := by ring
      rw [h6, h7] at h5
      linarith
    have h8 : f (4 - x) = - f (x - 1) := by
      have h9 : f (2 + (2 - x)) = - f (1 - (2 - x)) := by
        apply h2
      have h10 : (2 + (2 - x) : ℝ) = (4 - x : ℝ) := by ring
      have h11 : (1 - (2 - x) : ℝ) = (x - 1 : ℝ) := by ring
      rw [h10, h11] at h9
      linarith
    linarith

  have h4 : ∀ (k : ℝ), f (k + 1) = - f k := by
    intro k
    specialize h3 (k + 1)
    have h5 : (k + 1 : ℝ) = (k + 1 : ℝ) := by rfl
    have h7 : (k + 1 - 1 : ℝ) = k := by ring
    rw [h7] at h3
    linarith

  have h7 : ∀ (i : ℕ), f (i + 1 : ℝ) = (-1 : ℝ) ^ i * f 1 := by
    intro i
    induction i with
    | zero =>
      norm_num
    | succ i ih =>
      have h9 : (↑(i + 1 : ℕ) + 1 : ℝ) = (↑i + 1 : ℝ) + 1 := by
        simp at *
        all_goals ring_nf
      rw [h9]
      have h10 : f ((↑i + 1 : ℝ) + 1 ) = - f ((↑i + 1 : ℝ) ) := by
        specialize h4 ((↑i + 1 : ℝ) )
        simpa using h4
      rw [h10, ih]
      ring_nf

  have h9 : ∀ (i : ℕ), f (i + 1 : ℝ) = (-1 : ℝ) ^ i * f 1 := h7

  rw [Finset.sum_congr rfl (fun i _ => h9 i)]
  norm_num [Finset.sum_range_succ]
  <;> ring_nf