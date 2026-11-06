import Mathlib

/- Two positive rational numbers $x$ and $y$, when written in lowest terms, have the property that the sum of their numerators is 9 and the sum of their denominators is 10 . What is the largest possible value of $x+y$ ?-/
theorem number_theory_611262 :
    IsGreatest {z : ℚ | ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ Nat.gcd a b = 1 ∧ Nat.gcd c d = 1 ∧ a + c = 9 ∧ b + d = 10 ∧ z = a / b + c / d} (73 / 9) := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds, -one_div]
  refine ⟨?_,?_⟩
  . -- Prove that 73 / 9 is possible.
    -- A possible value of (x, y) is (8 / 1, 1 / 9).
    use 8, by norm_num, 1, by norm_num, 1, by norm_num, 9
    norm_num
  . -- Show that it could not be anything greater.
    intro z a ha b hb c hc d hd h₀ h₁ h₂ h₃ h₄
    rw [h₄]
    clear z h₄
    -- We have a < 9 and b < 10.
    have ha' : a < 9 := by
      omega
    have hb' : b < 10 := by
      omega
    rw [add_comm] at h₂ h₃
    apply Nat.eq_sub_of_add_eq at h₂
    apply Nat.eq_sub_of_add_eq at h₃
    -- Substitute c = 9 - a and d = 10 - b into the original equation.
    rw [h₂, h₃]
    -- Split into different cases and verify each by norm_num.
    interval_cases a
    <;> interval_cases b
      <;> norm_num
