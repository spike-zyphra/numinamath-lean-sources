import Mathlib

theorem algebra_1270 {f : ℝ → ℝ} (h : ∀ x, f (f x - x ^ 2 + x) = f x - x ^ 2 + x) :
    (f 2 = 3 → f 1 = 2 ∧ f 0 = 0) ∧
    (∃! t, f t = t) → f = (fun x => x ^ 2 - x) ∨ f = (fun x => x ^ 2 - x + 1) := by
  intro h1
  rcases h1 with ⟨h1, h2⟩
  rcases h2 with ⟨t, ht1, ht2⟩
  have h3 : ∀ x, f x - x ^ 2 + x = t := by
    intro x 
    have eq1 := h x
    have eq2 : f (f x - x ^ 2 + x) = f x - x ^ 2 + x := by
      simpa using eq1
    have h4 : f (f x - x ^ 2 + x) = (f x - x ^ 2 + x) := by 
      simpa using eq1
    have h6 : ∀ s, f s = s → s = t := ht2
    have h7 := h6 (f x - x ^ 2 + x) h4 
    linarith 
  have h4 : ∀ x, f x = x ^ 2 - x + t := by
    intro x 
    have eq1 := h3 x
    linarith 
  have ht3 : f t = t := ht1 
  have ht4 : f t = t ^ 2 - t + t := by 
    apply h4 
  have ht5 : t ^ 2 = t := by 
    nlinarith [ht3, ht4] 
  have ht6 : t = 0 ∨ t = 1 := by
    have : t * (t - 1) = 0 := by
      nlinarith 
    cases (mul_eq_zero.mp this) with
    | inl h7 =>
      left 
      linarith 
    | inr h8 =>
      right 
      linarith 
  cases ht6 with
  | inl ht7 =>
    have h7 : ∀ x, f x = x ^ 2 - x := by
      intro x 
      specialize h4 x 
      rw [show t = (0 : ℝ) by linarith [ht7] ] at h4 
      linarith 
    left 
    funext x 
    specialize h7 x 
    simpa using h7 
  | inr ht8 =>
    have h8 : ∀ x, f x = x ^ 2 - x + 1 := by 
      intro x 
      specialize h4 x 
      rw [show t = (1 : ℝ) by linarith [ht8] ] at h4 
      linarith 
    right 
    funext x 
    specialize h8 x 
    simpa using h8