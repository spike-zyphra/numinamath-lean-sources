import Mathlib

theorem algebra_295079 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + a * x + b)
    (ht : ∃ t, f t = 0 ∧ f (f (f t)) = 0) : f 0 * f 1 = 0 := by
  rcases ht with ⟨t, ⟨ht1, ht2⟩⟩
  have h1 : f t = 0 := ht1
  have h2 : f (f (f t)) = 0 := ht2
  have ht3 : f (f (f t)) = f (f 0) := by 
    rw [show f t = 0 by linarith [h1]]
  have ht4 : f (f 0) = 0 := by
    linarith [h2, ht3]
  have h6 : f 0 = b := by
    rw [hf 0]
    all_goals norm_num
  have h7 : f (f 0) = 0 := ht4
  rw [h6] at h7
  simp [hf] at h7 
  have h8 : b * (b + a + 1) = 0 := by
    nlinarith 
  cases (mul_eq_zero.mp h8) with
  | inl hb1 =>
    have h9 : f 0 = 0 := by 
      rw [h6]
      linarith [hb1]
    rw [h9]
    simp [hf 1]
    <;> nlinarith
  | inr hb2 =>
    have h10 : f 1 = 0 := by 
      rw [hf 1]
      nlinarith
    rw [h10]
    simp [hf 0]
    <;> nlinarith
  all_goals nlinarith