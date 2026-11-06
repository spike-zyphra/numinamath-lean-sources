import Mathlib

theorem algebra_11149 {a : ℝ} (ha : a > 0) (f g : ℝ → ℝ)
    (hf : f = fun x => x ^ 2 + 8) (hg : g = fun x => x ^ 2 - 4) :
    f (g a) = 8 ↔ a = 2 := by
  simp only [hf, hg]
  constructor
  · intro h
    have : (a ^ 2 - 4) ^ 2 = 0 := by linarith
    have : a ^ 2 - 4 = 0 := by
      rw [sq_eq_zero_iff] at this
      exact this
    have : a ^ 2 = 4 := by linarith
    have : a = 2 ∨ a = -2 := by
      have h1 : a = 2 ∨ a = -2 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        norm_num
        linarith
      exact h1
    rcases this with (rfl | h2)
    · rfl
    · linarith
  intro h
  rw [h]
  norm_num