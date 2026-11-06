import Mathlib

theorem algebra_238925 {f : ℝ → ℝ} (h₀ : ∀ x, f x > 0) (h₁ : ∀ a b, f a * f b = f (a + b)) :
    f 0 = 1 ∧ ∀ a, f (-a) = 1 / f a ∧ ∀ a, f a = (f (3 * a)) ^ ((1 : ℝ) / 3) := by

  have h1 : f 0 = 1 := by
    have h2 : f 0 * f 0 = f (0 + 0) := h₁ 0 0
    have h3 : f (0 + 0) = f 0 := by simp
    rw [h3] at h2
    have h4 : f 0 > 0 := h₀ 0
    nlinarith

  have h2 : ∀ a, f (-a) = 1 / f a := by
    intro a
    have h3 : f a * f (-a) = f (a + (-a)) := by
      apply h₁
    have h4 : a + (-a) = (0 : ℝ) := by
      ring
    rw [h4] at h3
    rw [h1] at h3
    have h5 : f a > 0 := h₀ a
    have h6 : f (-a) = 1 / f a := by
      field_simp [h5] at *
      nlinarith
    exact h6

  have h3 : ∀ a, f a = (f (3 * a)) ^ ((1 : ℝ) / 3) := by
    intro a
    have h4 : f (3 * a) = (f a) ^ 3 := by
      calc
        f (3 * a) = f (2 * a + a) := by ring_nf
        _ = f (2 * a) * f a := by
          rw [h₁ (2 * a) a]
          <;> ring_nf
        _ = (f (a + a) ) * f a := by
          have h5 : f (2 * a) = f (a + a) := by ring_nf
          rw [h5]
        _ = (f a * f a) * f a := by
          rw [h₁ a a]
          <;> ring_nf
        _ = (f a) ^ 3 := by
          ring

    have h7 : (f (3 * a) ) ^ ((1 : ℝ) / 3) = f a := by
      have h12 : f (3 * a) = (f a) ^ 3 := h4
      rw [h12]
      have h14 : ((f a) ^ 3) ^ ((1 : ℝ) / 3) = (f a) := by
        have h17 : ((f a) ^ 3) ^ ((1 : ℝ) / 3) = (f a) ^ (3 * ((1 : ℝ) / 3) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals nlinarith [h₀ a]
        rw [h17]
        norm_num
      linarith

    linarith [h7]

  exact ⟨h1, fun a => ⟨h2 a, fun a => h3 a⟩⟩