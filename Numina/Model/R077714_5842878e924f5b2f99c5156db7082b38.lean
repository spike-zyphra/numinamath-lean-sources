import Mathlib

theorem number_theory_242586 (a : ℕ) :
    (a = 1 ∨ a = 2 ∨ a = 4) → ∀ n : ℕ, n > 0 → ¬ ∃ m : ℕ, m^2 = n * (a + n) := by
  intro ha n hn
  rcases ha with (rfl | rfl | rfl)
  · -- Case a = 1: Show that n(1+n) is not a perfect square.
    intro h
    rcases h with ⟨m, hm⟩
    have h1 : m > n := by 
      nlinarith [sq_nonneg (m - n), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]
    have h2 : m < n + 1 := by 
      nlinarith [sq_nonneg (m - (n + 1)), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]
    omega
  · -- Case a = 2: Show that n(2+n) is not a perfect square.
    intro h
    rcases h with ⟨m, hm⟩
    have h1 : m > n := by
      nlinarith [sq_nonneg (m - n), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]
    have h2 : m < n + 1 := by 
      nlinarith [sq_nonneg (m - (n + 1)), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]
    omega
  · -- Case a = 4: Show that n(4+n) is not a perfect square.
    intro h
    rcases h with ⟨m, hm⟩
    have h1 : m > n := by
      nlinarith [sq_nonneg (m - n), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]
    have h2 : m < n + 2 := by 
      nlinarith [sq_nonneg (m - (n + 2)), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]
    nlinarith [sq_nonneg (m - (n + 1)), sq_nonneg (n : ℕ), sq_pos_of_pos (show 0 < n by omega)]