import Mathlib

/- When the two-digit integer $MM$, with equal digits, is multiplied by the one-digit integer $M$, the result is the three-digit integer $NPM$. What is the greatest possible value of $NPM$? -/
theorem number_theory_11609 : IsGreatest {m : ℕ | ∃ n : ℕ, m = n * (n % 10) ∧ 10 ≤ n ∧ n ≤ 99 ∧ m % 10 = n % 10 ∧ n / 10 = n % 10} 396 := by
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  . -- The first goal is to show that 396 satisfies the requirements.
    use 66
    simp
  . -- The second goal is to show that no numbers greater than 396 satisfies the requirements.
    intro m n h₀ _ _ h₃ h₄
    rw [h₀] at h₃
    rw [Nat.mul_mod, Nat.mod_mod] at h₃
    have h₅ : n % 10 < 10 := by
      apply Nat.mod_lt
      norm_num
    -- By trial and error on the unit digit.
    let M : ℕ := n % 10
    -- Prevent losing n % 10 after interval_cases.
    have g : M = n % 10 := by
      dsimp [M]
    interval_cases (n % 10)
    all_goals
      -- Try derive a contardiction by (n % 10) * (n % 10) % 10 = (n % 10).
      try simp at h₃
    . rw [h₀]
      norm_num
    . rw [h₀]
      omega
    . rw [h₀]
      omega
    . rw [h₀]
      replace g : n = 6 + 10 * (n / 10) := by
        rw [<-g, Nat.mod_add_div]
      rw [h₄] at g
      omega
