import Mathlib

theorem number_theory_249477 (a : ℕ → ℕ) (ha : ∀ n, a n ∈ Finset.Icc 1 8)
    (h : ∀ m n, a n ∣ n ∧ a m ∣ m ↔ a (m + n) = a m + a n - 1) :
    a 5555 = 1 := by 
  have h0 : a 0 = 1 := by 
    have h4 := h 0 0 
    simp [Nat.dvd_zero, Nat.zero_eq] at h4 
    have ha0 : a 0 ∈ Finset.Icc 1 8 := ha 0 
    simp at ha0 ⊢ 
    omega 
  have h1 : a 1 = 1 := by 
    have h6 := h 1 0 
    simp [Nat.dvd_zero, Nat.dvd_one] at h6 ⊢ 
    omega 
  have h2 : a 2 = 1 := by 
    have h8 := h 1 1 
    simp [h1, Nat.dvd_one] at h8 ⊢ 
    omega 
  -- Show $a_n$ divides $n$ for all $n$.
  have h12 : ∀ (n : ℕ), a n ∣ n := by 
    intro n 
    have eq6 := h 0 n 
    simp [Nat.dvd_zero, Nat.zero_eq] at eq6 ⊢ 
    omega 
  -- Show $a_{n+1} = a_n$ for all $n$.
  have h15 : ∀ n, a (n + 1) = a n := by 
    intro n 
    have eq5 := h n 1 
    have h12n : a n ∣ n := h12 n 
    simp [show a 1 = 1 by linarith [h1], h1, Nat.dvd_one, h12] at eq5 ⊢ 
    omega 
  -- Show $a_n = 1$ for all $n$ by induction.
  have h5 : ∀ n, a n = 1 := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero => 
      exact h0 
    | succ n => 
      cases n with 
      | zero => 
        exact h1 
      | succ n => 
        -- need to show a (n + 2) = 1
        have h15n : a (n + 1 + 1) = a (n + 1) := by 
          have eq5a := h15 (n + 1) 
          simpa using eq5a 
        rw [show n + 1 + 1 = (n + 1) + 1 by omega] 
        rw [h15n] 
        exact ih (n + 1) (by linarith) 
  -- Therefore $a_{5555} = 1$.
  specialize h5 5555 
  simpa using h5