import Mathlib

/- 31.3. Prove that there are infinitely many prime numbers of the form $4k+1$. -/
#check Nat.div_add_mod
theorem number_theory_230387 :
    ∀ n : ℕ, ∃ p > n, p.Prime ∧ ∃ k, p = 4 * k + 1 := by
  intro n
  -- Mathlib can handle this quite nicely
  have pmod4 := Nat.exists_prime_gt_modEq_one (k:=4) n (by norm_num)
  obtain ⟨p, hp, hnp, pmod⟩ := pmod4
  use p, hnp, hp
  simp [Nat.ModEq] at pmod
  use p / 4
  rw [← pmod]
  exact (Nat.div_add_mod p 4).symm