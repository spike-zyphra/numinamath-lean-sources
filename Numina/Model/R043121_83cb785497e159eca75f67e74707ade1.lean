import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21167 {f : ℝ → ℝ} (hf : f = λ x => (5 * x + 3) / x) :
    range f = {y | y ≠ 5} := by 
  ext y
  simp [hf, Set.mem_range]
  constructor 
  · -- Assume y ∈ range f, prove y ≠ 5
    rintro ⟨x, hx⟩
    by_contra h
    have h0 : x ≠ 0 := by
      by_contra h1
      have h1 : x = 0 := by
        linarith
      have hx0 : (5 * x + 3) / x = y := by
        linarith [hx]
      rw [h1] at hx0
      norm_num at hx0 
      have h05 : y = 0 := by
        linarith 
      linarith 
    have h2 : (5 * x + 3) / x = 5 := by 
      rw [show y = 5 by linarith [h] ] at hx 
      linarith
    have h4 : x ≠ 0 := h0 
    have h5 : 5 * x + 3 = 5 * x := by
      have eq1 : (5 * x + 3) / x = 5 := by 
        linarith [h2]
      have h7 : x ≠ 0 := h4
      have eq2 : 5 * x + 3 = 5 * x := by 
        have h8 : x ≠ 0 := h7 
        field_simp [h8] at eq1 ⊢
        all_goals linarith
      assumption
    exfalso 
    linarith 
  · -- Assume y ≠ 5, prove y ∈ range f
    intro hy 
    have h4 : y - 5 ≠ 0 := by 
      intro h5 
      apply hy 
      linarith 
    use 3 / (y - 5) 
    have h5 : y - 5 ≠ 0 := h4 
    field_simp [h5] 
    <;> ring