import Mathlib

theorem algebra_106920 {x : ℝ} (hx : x ≠ 0) (h : ∃ n : ℤ, x + 1/x = n) :
    ∀ n : ℕ, ∃ m : ℤ, x^n + 1/x^n = m := by
  rcases h with ⟨n₀, h₀⟩
  intro n
  have h1 : ∀ (n : ℕ), ∃ m : ℤ, x ^ n + 1 / x ^ n = m := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      use (2 : ℤ)
      field_simp [hx]
      <;> norm_num
    | succ n =>
      cases n with 
      | zero =>
        use n₀
        field_simp at h₀ ⊢
        <;> nlinarith
      | succ n =>
        rcases ih (n) (by linarith) with ⟨m₁, hm₁⟩
        rcases ih (n + 1) (by linarith) with ⟨m₂, hm₂⟩
        have eq1 : x ^ (n + 1 + 1) + 1 / x ^ (n + 1 + 1) = (x + 1 / x) * (x ^ (n + 1) + 1 / x ^ (n + 1)) - (x ^ n + 1 / x ^ n) := by
          field_simp at *
          ring 
        use n₀ * m₂ - m₁ 
        rw [eq1]
        rw [h₀]
        rw [hm₂]
        rw [hm₁]
        all_goals norm_num at *
        <;> ring_nf 
  specialize h1 n 
  simpa using h1