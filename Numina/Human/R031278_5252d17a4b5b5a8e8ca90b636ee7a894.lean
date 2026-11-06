import Mathlib

theorem number_theory_292952 (u : ℕ → ℤ) (h : Function.Periodic u 2022) (h' : Function.Periodic u 5) :
    ∃ c, ∀ n, u n = c := by
  have h1 : ∀ n, u (n + 2022) = u n := by
    intro n
    exact h n
  have h2 : ∀ n, u (n + 5) = u n := by
    intro n
    exact h' n

  have h_const : ∀ n, u n = u 0 := by
    intro n
    have h3 : ∀ n, u (n + 1) = u n := by
      intro n
      have h4 := h2 (n + 1)
      have h5 := h1 (n + 6066)
      norm_num at h4 h5
      have h6 : u (n + 1) = u (n + 6066) := by
        have h5 : ∀ k, u (n + 1 + 5 * k) = u (n + 1) := by
          intro k
          induction k with
          | zero =>
            simp
          | succ k ih =>
            calc
              u (n + 1 + 5 * (k + 1)) = u (n + 1 + 5 * k + 5) := by ring
              _ = u (n + 1 + 5 * k) := by apply h2
              _ = u (n + 1) := by linarith [ih]
        have h6 := h5 1213
        norm_num at h6
        linarith
      have h7 : u (n + 6066) = u n := by
        have h8 : u (n + 2022) = u n := by
          exact h1 n
        have h9 : u (n + 4044) = u (n + 2022) := by
          exact h1 (n + 2022)
        have h10 : u (n + 6066) = u (n + 4044) := by
          exact h1 (n + 4044)
        linarith
      linarith
    have h4 : u n = u 0 := by
      induction n with
      | zero =>
        simp
      | succ m ih =>
        have h5 : u (m + 1) = u m := by
          exact h3 m
        rw [ih] at h5
        linarith
    exact h4

  exact ⟨u 0, fun n => h_const n⟩