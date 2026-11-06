import Mathlib

theorem number_theory_283227 (n : ℕ) (s : ℕ → ℕ)
    (hs : ∀ m, s m = (Nat.digits 10 m).sum) (hn : ∃ k, s^[k] = 2 ∨ s^[k] = 3
    ∨ s^[k] = 5 ∨ s^[k] = 6) : ¬ ∃ r, n = r ^ 2 ∨ n = r ^ 3 := by
  rcases hn with ⟨k, hk⟩
  intro h
  rcases h with ⟨r, hr⟩
  have h1 : n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 5 ∨ n % 9 = 6 := by
    have h2 : ∀ (m : ℕ), s m % 9 = m % 9 := by
      intro m
      have h4 : s m = (Nat.digits 10 m).sum := hs m
      rw [h4]
      have h3 : m % 9 = (Nat.digits 10 m).sum % 9 := by
        rw [Nat.modEq_nine_digits_sum (m)]
      omega
    have h3 : ∀ (k : ℕ), (s^[k] n) % 9 = n % 9 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp [Function.iterate_succ_apply'] at ih ⊢
        all_goals
          have h11 : s (s^[k] n) % 9 = (s^[k] n) % 9 := by
            apply h2
          omega
    have h10 : (s^[k] n) % 9 = n % 9 := h3 k
    rcases hk with (h | h | h | h)
    · -- s^[k] n = 2
      have h2' : (s^[k] n) % 9 = 2 := by 
        rw [h]
        all_goals simp
      omega
    · -- s^[k] n = 3
      have h3' : (s^[k] n) % 9 = 3 := by 
        rw [h]
        all_goals simp
      omega
    · -- s^[k] n = 5
      have h5' : (s^[k] n) % 9 = 5 := by 
        rw [h]
        all_goals simp
      omega
    · -- s^[k] n = 6
      have h6' : (s^[k] n) % 9 = 6 := by 
        rw [h]
        all_goals simp
      omega
  rcases hr with (h11 | h11)
  · -- n = r ^ 2
    have h12 : n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 5 ∨ n % 9 = 6 := h1
    have h13 : r ^ 2 % 9 = 0 ∨ r ^ 2 % 9 = 1 ∨ r ^ 2 % 9 = 4 ∨ r ^ 2 % 9 = 7 ∨ r ^ 2 % 9 = 9 := by
      have h14 : r % 9 = 0 ∨ r % 9 = 1 ∨ r % 9 = 2 ∨ r % 9 = 3 ∨ r % 9 = 4 ∨ r % 9 = 5 ∨ r % 9 = 6 ∨ r % 9 = 7 ∨ r % 9 = 8 := by
        omega
      rcases h14 with (h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h]
    have h14 : n % 9 = r ^ 2 % 9 := by 
      rw [show n = r ^ 2 by linarith [h11]]
    omega
  · -- n = r ^ 3
    have h112 : n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 5 ∨ n % 9 = 6 := h1
    have h113 : r ^ 3 % 9 = 0 ∨ r ^ 3 % 9 = 1 ∨ r ^ 3 % 9 = 8 := by
      have h14 : r % 9 = 0 ∨ r % 9 = 1 ∨ r % 9 = 2 ∨ r % 9 = 3 ∨ r % 9 = 4 ∨ r % 9 = 5 ∨ r % 9 = 6 ∨ r % 9 = 7 ∨ r % 9 = 8 := by
        omega
      rcases h14 with (h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Nat.mul_mod, h]
    have h114 : n % 9 = r ^ 3 % 9 := by 
      rw [show n = r ^ 3 by linarith [h11]]
    omega