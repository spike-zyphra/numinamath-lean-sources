import Mathlib

theorem inequalities_135800 (n : ℕ) (hn : 0 < n) (a A : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hA : ∀ i, 0 < A i) :
    (∑ i, a i * A i) * (∑ i, a i / A i) ≥ (∑ i, a i) ^ 2 := by

  have h3 : ∀ i, 0 < a i := ha
  have h4 : ∀ i, 0 < A i := hA
  have h5 : ∀ i, 0 < a i * A i := by
    intro i
    have ha1 : 0 < a i := h3 i
    have hA1 : 0 < A i := h4 i
    positivity

  have h6 : ∀ i, 0 < a i / A i := by
    intro i
    have ha1 : 0 < a i := h3 i
    have hA1 : 0 < A i := h4 i
    apply div_pos
    all_goals linarith

  have h7 : (∑ i, a i) ^ 2 ≤ (∑ i, a i * A i) * (∑ i, a i / A i) := by
    have h71 : ∀ i, √(a i * A i) * √(a i / A i) = a i := by
      intro i
      have ha1 : 0 < a i := h3 i
      have hA1 : 0 < A i := h4 i
      have h11 : a i * A i > 0 := by positivity
      have h12 : a i / A i > 0 := by positivity
      have h21 : (√(a i * A i) * √(a i / A i)) = √((a i * A i) * (a i / A i)) := by 
        rw [← Real.sqrt_mul (by positivity)]
      have h22 : (a i * A i) * (a i / A i) = (a i) ^ 2 := by
        field_simp [show 0 < A i by assumption]
        <;> ring
      have h23 : √((a i) ^ 2) = a i := by
        rw [Real.sqrt_sq (show 0 ≤ a i by linarith)]
      rw [h21, h22, h23]
      all_goals nlinarith

    have h13 : (∑ i, (√(a i * A i) * √(a i / A i))) ^ 2 ≤ (∑ i, (√(a i * A i)) ^ 2) * (∑ i, (√(a i / A i)) ^ 2) := by 
      apply Finset.sum_mul_sq_le_sq_mul_sq

    have h14 : ∑ i, (√(a i * A i) * √(a i / A i)) = ∑ i, (a i) := by 
      congr
      funext i
      exact h71 i

    have h15 : ∑ i, (√(a i * A i)) ^ 2 = ∑ i, (a i * A i) := by 
      apply Finset.sum_congr rfl
      intro i hi
      have ha1 : 0 < a i := h3 i
      have hA1 : 0 < A i := h4 i
      have h16 : (√(a i * A i)) ^ 2 = a i * A i := by
        rw [Real.sq_sqrt]
        positivity
      linarith

    have h16 : ∑ i, (√(a i / A i)) ^ 2 = ∑ i, (a i / A i) := by 
      apply Finset.sum_congr rfl
      intro i hi
      have ha1 : 0 < a i := h3 i
      have hA1 : 0 < A i := h4 i
      have h17 : (√(a i / A i)) ^ 2 = a i / A i := by
        rw [Real.sq_sqrt]
        positivity
      linarith

    rw [h14] at h13
    rw [h15, h16] at h13
    nlinarith

  linarith
  all_goals nlinarith
  all_goals try { linarith [h7, sq_nonneg (∑ i, a i * A i), sq_nonneg (∑ i, a i / A i) ] }
  all_goals try { aesop }