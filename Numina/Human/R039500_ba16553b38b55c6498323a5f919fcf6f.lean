import Mathlib

/- If $p$ and $q$ are positive integers and $\frac{2008}{2009}<\frac{p}{q}<\frac{2009}{2010}$, what is the minimum value of $p$ ?-/
theorem number_theory_608433 :
    IsLeast {p : ℕ | 0 < p ∧ ∃ q : ℕ, 0 < q ∧ 2008 / (2009 : ℚ) < p / (q : ℚ) ∧ p / (q : ℚ) < 2009 / (2010 : ℚ)} 4017 := by
  -- Simplify the goal into two parts.
  simp only [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Prove that 4017 is possible, because we can take q = 4019.
    simp
    use 4019
    norm_num
  . -- Prove that p cannot be anything smaller.
    intro p h
    obtain ⟨hp, q, hq, h₀, h₁⟩ := h
    -- Multiply out the fraction inequalities h₀ and h₁.
    rw [div_lt_iff₀, mul_comm, <-mul_div_assoc, lt_div_iff₀] at h₀ h₁
    norm_cast at h₀ h₁
    rw [<-Nat.add_one_le_iff] at h₀ h₁
    -- Multiply h₀ by 2009 and h₁ by 2008.
    apply Nat.mul_le_mul_left 2009 at h₀
    apply Nat.mul_le_mul_left 2008 at h₁
    -- Combine the two inequalities.
    have h₂ : 2008 * (p * 2010) + 2008 + 2009 ≤ 2009 * (2009 * p) := by
      calc
        2008 * (p * 2010) + 2008 + 2009 ≤ 2008 * (q * 2009) + 2009 := by
          apply Nat.add_le_add_right
          rw [<-Nat.mul_add_one]
          exact h₁
        _ = 2009 * (2008 * q + 1) := by
          ring
        _ ≤ 2009 * (2009 * p) := h₀
    -- We have p ≥ 4017.
    linarith
    all_goals
      positivity
