import Mathlib

theorem algebra_109336 {a : ℕ → ℤ}
    (ha : ∀ n, a (n + 2) = 5 * a (n + 1) - 6 * a n + 4 ^ (n + 1))
    (ha0 : a 0 = 1) (ha1 : a 1 = 3) :
    ∀ n, a n = 2 ^ (n + 1) - 3 ^ (n + 1) + 2 * 4 ^ n := by
  intro n
  have h : ∀ m ≤ n, a m = 2 ^ (m + 1) - 3 ^ (m + 1) + 2 * 4 ^ m := by
    induction n with
    | zero =>
      intro m hm
      cases m with
      | zero => simp [ha0]
      | succ m => linarith
    | succ n ih =>
      intro m hm
      cases m with
      | zero => simp [ha0]
      | succ m =>
        cases m with
        | zero =>
          simp [ha1]
        | succ m =>
          have h1 : m ≤ n := by linarith
          have ih1 := ih m h1
          have ih2 := ih (m + 1) (by linarith)
          have h2 := ha m
          simp [show m + 2 = (m + 1) + 1 by rfl] at h2
          simp [h2, ih1, ih2]
          ring
      all_goals linarith
  have hn := h n (by linarith)
  exact hn