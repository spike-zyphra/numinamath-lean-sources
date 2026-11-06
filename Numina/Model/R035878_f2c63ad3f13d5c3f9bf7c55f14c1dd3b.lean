import Mathlib

theorem algebra_9274 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x * abs (x - a) + b) :
    (∀ x : ℝ, f x = - f (-x)) ↔ a ^ 2 + b ^ 2 = 0 := by
  constructor
  · -- First implication: If $f$ is odd, then $a^2 + b^2 = 0$.
    intro h
    have h0 := h 0
    simp [hf] at h0
    have hb : b = 0 := by linarith
    have h1 := h 1
    have h2 := h (-1 : ℝ)
    simp [hf, hb] at h1 h2
    have ha : a = 0 := by
      have h3 : abs (1 - a) = abs (-1 - a) := by linarith
      cases abs_eq_abs.1 h3 with
      | inl h_eq =>
        linarith
      | inr h_eq =>
        linarith
    rw [ha, hb]
    norm_num
  · -- Second implication: If $a^2 + b^2 = 0$, then $f$ is odd.
    intro h
    have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    intro x
    have hfx : f x = x * abs (x - a) + b := hf x
    have hf_neg_x : f (-x) = (-x) * abs (-x - a) + b := hf (-x)
    rw [hfx, hf_neg_x]
    rw [ha, hb]
    simp [abs_neg]
    <;> ring