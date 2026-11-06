import Mathlib

theorem number_theory_4487 : {p : ℕ | p.Prime ∧ ∃ a b, p = a ^ 4 - b ^ 4} = ∅ := by
  rw [Set.eq_empty_iff_forall_not_mem]
  -- there is no prime number can be expressed as a^4-b^4
  intro p ⟨hp, a, b, h⟩
  -- deduce `b≤a` from `a^4-b^4=p≥2`
  have hba : b ≤ a := by
    by_contra! lt
    rw [Nat.sub_eq_zero_of_le (Nat.pow_le_pow_of_le_left (le_of_lt lt) 4)] at h
    norm_num [h] at hp
  -- factor `a^4-b^4` to `(a-b)(a+b)(a^2+b^2)`
  replace h : p = (a - b) * (a + b) * (a ^ 2 + b ^ 2) := by
    rw [h]
    zify [Nat.pow_le_pow_of_le_left hba, hba]
    ring
  -- Notice that p is prime, it must be `a+b=1` or `a^2+b^2=1`
  have h₁ : a + b = 1 ∨ a ^ 2 + b ^ 2 = 1 := by
    contrapose! hp with h₂
    refine Nat.not_prime_mul' h.symm ?_ h₂.2
    exact mul_ne_one.mpr (.inr h₂.1)
  -- If `a=0,b=1` or `a=1,b=0`, then `p` is not prime.
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0 := by
    rcases h₁ with h₁ | h₁
    . rwa [Nat.add_eq_one_iff] at h₁
    . simpa [Nat.add_eq_one_iff, pow_eq_one_iff] using h₁
  . simp at hba
  . simp [h, Nat.not_prime_one] at hp
