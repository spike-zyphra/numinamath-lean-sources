import Mathlib

theorem algebra_97927 {f : ℝ → ℝ} (h₀ : ∀ x, f x > 0)
    (h₁ : ∀ a b, f a * f b = f (a + b)) :
    f 0 = 1 ∧ ∀ a, f (-a) = 1 / f a ∧ ∀ a, f a = (f (3 * a)) ^ ((1 : ℝ) / 3) := by 
  have h1 : f 0 = 1 := by
    have h2 := h₁ 0 0
    simp at h2
    nlinarith [h₀ 0]
  have h3 : ∀ a, f (-a) = 1 / f a := by
    intro a 
    have h4 : f a * f (-a) = f (a + (-a)) := by 
      apply h₁ 
    have h5 : a + (-a) = (0 : ℝ) := by 
      ring 
    rw [h5] at h4 
    rw [h1] at h4 
    have h6 : f a > 0 := h₀ a 
    have h7 : f (-a) = 1 / f a := by 
      field_simp [h6] at h4 ⊢
      linarith 
    exact h7 
  have h4 : ∀ a, f a = (f (3 * a)) ^ ((1 : ℝ) / 3) := by 
    intro a
    have h5 : f (2 * a) = (f a) ^ 2 := by 
      calc 
        f (2 * a) = f (a + a) := by ring_nf 
        _ = f a * f a := by 
          rw [h₁ a a] 
        _ = (f a) ^ 2 := by ring 
    have h6 : f (3 * a) = (f a) ^ 3 := by 
      calc 
        f (3 * a) = f (2 * a + a) := by ring_nf 
        _ = f (2 * a) * f a := by
          rw [h₁ (2 * a) a] 
        _ = (f a) ^ 2 * f a := by 
          rw [h5] 
        _ = (f a) ^ 3 := by 
          ring 
    have h7 : f (3 * a) = (f a) ^ 3 := h6 
    have h8 : f a = ((f a) ^ 3) ^ ((1 : ℝ) / 3) := by 
      have h9 : (( (f a) ^ 3 ) ^ ((1 : ℝ) / 3) ) = (f a) := by 
        have h10 : ( (f a) ^ 3 ) ^ ((1 : ℝ) / 3) = (f a) ^ (3 * ((1 : ℝ) / 3) ) := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring 
          all_goals linarith [h₀ a] 
        have h11 : (f a) ^ (3 * ((1 : ℝ) / 3) ) = (f a) := by 
          have h12 : 3 * ((1 : ℝ) / 3) = 1 := by 
            ring 
          rw [h12]
          all_goals simp 
        rw [h10, h11] 
      linarith 
    rw [h7] at *
    linarith 
  exact ⟨h1, fun a => ⟨h3 a, fun a => h4 a⟩⟩