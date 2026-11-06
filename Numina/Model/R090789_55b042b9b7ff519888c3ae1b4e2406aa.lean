import Mathlib

theorem number_theory_19077 {F : ℕ → ℕ} (hF : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    IsGreatest {x | ∃ n, x = Nat.gcd (F n) (F (n + 1))} 1 := by

  constructor
  · -- Show 1 is in the set.
    use 0
    simp [hF0, hF1]
  · -- Show that any element in the set is ≤1.
    rintro x ⟨n, hn⟩
    rw [hn]
    have h1 : ∀ n, (Nat.gcd (F n) (F (n + 1)) ) = 1 := by
      intro n
      induction' n using Nat.strongRec with n ih
      cases n with
      | zero =>
        simp [hF0, hF1, Nat.gcd_comm]
      | succ n =>
        have h0 : Nat.gcd (F n) (F (n + 1)) = 1 := by
          apply ih
          all_goals omega
        simp [hF, h0, Nat.gcd_comm, Nat.gcd_add_self_right]
        all_goals omega
    have h3 : (Nat.gcd (F n) (F (n + 1)) ) = 1 := h1 n
    linarith