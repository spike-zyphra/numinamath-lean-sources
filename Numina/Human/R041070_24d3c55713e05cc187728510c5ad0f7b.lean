import Mathlib

/-What is the largest integer less than $2010$ that has a remainder of $5$ when divided by $7,$ a remainder of $10$ when divided by $11,$ and a remainder of $10$ when divided by $13$?-/
theorem number_theory_22695 :
    IsGreatest {x | x < 2010 ∧ x % 7 = 5 ∧ x % 11 = 10 ∧ x % 13 = 10} 1440 := by
  constructor
  · -- Prove that: 1440 is in the set
    simp
  · apply mem_upperBounds.mpr
    -- Prove that: 1440 is an upper bound
    simp
    intro x hx₁ hx₂ hx₃ hx₄
    -- We want a remainder of $10$ when divided by both $11$ and $13$. The least common multiple of $11$ and $13$ is $143$. We add $10$ to the number such that the remainder would be $10$ when divided by $11$ and $13$
    have h₁ : x % 143 = 10 := by
      rw [show 143 = Nat.lcm 11 13 by rfl]
      apply Nat.mod_eq_of_modEq
      exact Nat.mod_lcm hx₃ hx₄
      norm_num
    have hx₅ : 10 ≤ x := by
      by_contra! h
      have : x % 11 = x := by
        apply Nat.mod_eq_of_lt (by linarith)
      rw [this] at hx₃
      linarith

    -- However, that does not give a remainder of $5$ when divided by $7$, so we add more $143$s until we get a value that works. We get that $153+143+143=439$ gives a remainder of $5$ when divided by $7$.
    -- Since we want the largest integer less than 2010, we keep adding the least common multiple of $7$, $11$, and $13$ until we go over. The least common multiple is $7 \cdot 11 \cdot 13 =1001$. We add it to $439$ to get $1440$, adding it again would give a value greater than $2010$, so our answer is $\boxed{1440}$.
    obtain ⟨k, hk⟩ := show ∃k, x = 143 * k + 10 by
      use (x - 10) / 143
      apply (Nat.sub_eq_iff_eq_add hx₅).mp
      apply Nat.eq_mul_of_div_eq_right ?_ rfl
      apply (Nat.modEq_iff_dvd' hx₅).mp
      exact (Eq.symm h₁)
    have : k ≤ 10 := by omega
    rw [hk] at hx₁ hx₂ hx₃ hx₄
    interval_cases k
    all_goals
      simp at hx₁ hx₂ hx₃ hx₄
    rw [hk]; norm_num
    rw [hk]
