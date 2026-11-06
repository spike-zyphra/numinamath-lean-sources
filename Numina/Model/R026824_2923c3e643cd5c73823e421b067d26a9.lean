import Mathlib

theorem algebra_106168 {x : ℝ} (hx : x ≠ 0) (h : ∃ n : ℤ, x + 1 / x = n) (n : ℕ) :
    ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
  have h1 : ∀ (n : ℕ), ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      use 2
      norm_num
    | succ n =>
      cases n with
      | zero => -- This is the case for n=1
        rcases h with ⟨n, hn⟩
        use n
        field_simp [hx] at hn ⊢
        linarith
      | succ n => -- This is the case for n ≥ 2
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        rcases h with ⟨k, hk⟩
        rcases h2 with ⟨m2, hm2⟩
        rcases h3 with ⟨m3, hm3⟩
        use k * m2 - m3
        have eq4 : x ^ (n + 2) + 1 / x ^ (n + 2) = (x + 1 / x) * (x ^ (n + 1) + 1 / x ^ (n + 1)) - (x ^ n + 1 / x ^ n) := by
          field_simp [hx]
          <;> ring_nf 
        rw [eq4, hk, hm2, hm3]
        all_goals norm_num
  specialize h1 n
  simpa using h1