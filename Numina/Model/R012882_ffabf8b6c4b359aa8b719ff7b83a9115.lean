import Mathlib

theorem algebra_274845 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = (5 * a n - 13) / (3 * a n - 7)) :
    ∀ n ≥ 1, a (n + 3) = a n := by 
  intro n hn
  have base1 : a 4 = a 1 := by 
    have ha2 : a 2 = (5 * a 1 - 13) / (3 * a 1 - 7) := han 1 (by linarith)
    rw [ha1] at ha2
    norm_num at ha2
    have ha3 : a 3 = (5 * a 2 - 13) / (3 * a 2 - 7) := han 2 (by linarith)
    rw [ha2] at ha3
    norm_num at ha3
    have ha4 : a 4 = (5 * a 3 - 13) / (3 * a 3 - 7) := han 3 (by linarith)
    rw [ha3] at ha4
    norm_num at ha4
    rw [ha4, ha1]
  have step1 : ∀ k ≥ 1, a (k + 3) = a k → a (k + 1 + 3) = a (k + 1) := by
    intro k hk h
    have h1 : a (k + 1 + 3) = (5 * a (k + 3) - 13) / (3 * a (k + 3) - 7) := by
      specialize han (k + 3) (by linarith)
      simpa using han
    rw [h1]
    rw [h]
    have h2 : a (k + 1) = (5 * a k - 13) / (3 * a k - 7) := by
      specialize han k (by linarith)
      simpa using han
    rw [h2]
  exact Nat.le_induction base1 step1 n (by linarith)