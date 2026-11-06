import Mathlib

theorem algebra_214457 {f : ℕ → ℕ} (h : ∀ x y, x > 0 → y > 0 → f (x + y) = f x * f y)
    (hf : f 1 = 2) : f 2007 = 2 ^ 2007 := by
  have h1 : ∀ k, f (k + 1) = 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      simp [hf]
    | succ k ih =>
      have eq1 : f ((k + 1) + 1) = f (k + 1) * f 1 := h (k + 1) 1 (by linarith) (by norm_num)
      rw [hf] at eq1 -- replace f(1) by 2
      rw [eq1]
      rw [ih]
      ring_nf
      all_goals omega
  have : f 2007 = 2 ^ 2007 := by
    specialize h1 2006
    norm_num at h1 ⊢
    exact h1
  exact this