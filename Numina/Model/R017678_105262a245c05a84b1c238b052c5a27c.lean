import Mathlib

theorem algebra_272824 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : ∀ n, a (n + 2) = a n * a (n + 1)) :
    (∀ n, a (n + 1) = a n) ↔ a 1 = 1 ∧ a 2 = 1 := by
  constructor
  · -- Assume $∀ n, a (n + 1) = a n)$, prove $a 1 = 1 ∧ a 2 = 1$
    intro h_eq
    have ha1 : a 1 = 1 := by
      have h_eq1 : a 2 = a 1 := by
        specialize h_eq 1
        norm_num at h_eq ⊢
        all_goals linarith
      have h_eq2 : a 3 = a 1 * a 2 := by
        specialize h 1
        norm_num at h ⊢
        all_goals linarith
      have h_eq3 : a 3 = a 2 := by
        specialize h_eq 2
        norm_num at h_eq ⊢
        all_goals linarith
      rw [show a 3 = a 1 * a 2 by linarith [h_eq2]] at h_eq3
      rw [show a 2 = a 1 by linarith [h_eq1]] at h_eq3
      have ha_pos0 : 0 < a 0 := by
        apply ha 0
      have ha1_pos : 0 < a 1 := by
        apply ha 1
      have h_eq4 : a 1 * (a 1 - 1) = 0 := by
        nlinarith [h_eq3]
      cases' (mul_eq_zero.1 h_eq4) with h_eq5 h_eq6
      · -- Case $a 1 = 0$
        nlinarith [ha1_pos]
      · -- Case $a 1 - 1 = 0$
        linarith
    have ha2 : a 2 = 1 := by
      have h_eq1 : a 2 = a 1 := by
        specialize h_eq 1
        norm_num at h_eq ⊢
        all_goals linarith
      nlinarith [h_eq1, ha1]
    exact ⟨ha1, ha2⟩
  · -- Assume $a 1 = 1 ∧ a 2 = 1$, prove $∀ n, a (n + 1) = a n$
    rintro ⟨ha1, ha2⟩
    have h1 : ∀ n: ℕ, a n = 1 := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        have h0 : a 0 * a 1 = a 2 := by
          specialize h 0
          norm_num at h ⊢
          all_goals nlinarith
        rw [show a 1 = (1:ℝ) by linarith [ha1], show a 2 = (1:ℝ) by linarith [ha2]] at h0
        nlinarith
      | succ n =>
        cases n with
        | zero =>
          norm_num [ha1]
        | succ n =>
          have hn0 : a (n) = 1 := by
            specialize ih n (by linarith)
            all_goals linarith
          have hn1 : a (n + 1) = 1 := by
            specialize ih (n + 1) (by linarith)
            all_goals linarith
          have h2 : a (n + 2) = 1 := by
            have h3 : a (n + 2) = a (n) * a (n + 1) := by
              specialize h n
              simpa using h
            rw [h3, hn0, hn1]
            all_goals norm_num
          simpa using h2
    intro n
    have hn0 : a (n + 1) = 1 := by
      specialize h1 (n + 1)
      all_goals linarith
    have hn1 : a n = 1 := by
      specialize h1 n
      all_goals linarith
    linarith [hn0, hn1]