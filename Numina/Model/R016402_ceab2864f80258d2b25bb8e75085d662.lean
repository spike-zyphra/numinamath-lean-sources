import Mathlib

theorem algebra_179573 (a b : ℕ) (ha : a ∈ Finset.Icc 10 99) (hb : b ∈ Finset.Icc 10 99)
    (h : (a * 100 + b) = (a + b) ^ 2) :
    (a = 20 ∧ b = 25) ∨ (a = 30 ∧ b = 25) := by 
  rw [Finset.mem_Icc] at ha hb 
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  have h3 : a * 100 + b = (a + b) ^ 2 := h
  have h4 : b ≤ 25 := by
    nlinarith [sq_nonneg (a - 30 : ℤ), sq_nonneg (b - 25 : ℤ), sq_nonneg ((a + b) - 55 : ℤ), sq_nonneg ((a - 20 : ℤ)), sq_nonneg ((a - b) : ℤ)]
  interval_cases b <;> try { 
    have : a ≤ 99 := by linarith
    interval_cases a <;> norm_num at h ⊢ <;> tauto 
  }
  <;> norm_num at h ⊢
  <;> try { 
    nlinarith 
  }
  <;> tauto