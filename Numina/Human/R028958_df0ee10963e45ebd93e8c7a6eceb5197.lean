import Mathlib

/- 2. Can the number 2020 be represented as the sum of 99 natural numbers with the same digit sum? -/
theorem number_theory_161318 : ¬∃ n : ℕ, ∃ k : Fin 99 → ℕ,
    (∀ i, k i > 0) ∧
    (∑ i, k i) = 2020 ∧
    (∀ i, (Nat.digits 10 (k i)).sum = n) := by
  -- asuume such n and sequence of numbers nums exists
  by_contra h
  obtain ⟨n, nums, nums_pos, nums_sum, nums_digsum⟩ := h
  -- then that means sum of nums i % 3 mod 3 is equal to 2020 % 3 = 1
  replace nums_sum := congrArg (fun x ↦ x % 3) nums_sum
  simp at nums_sum
  rw [Finset.sum_nat_mod] at nums_sum
  -- now (nums i) % 3 = n % 3, as (nums i) % 3 = (digitsum of nums i) % 3
  have num_mod_3 (i : Fin 99) : nums i % 3 = n % 3 := by
    rw [← nums_digsum i, ← Nat.ModEq.eq_1]
    apply Nat.modEq_three_digits_sum
  -- then (99 * n) % 3 = 1, but that's false
  simp_rw [num_mod_3] at nums_sum
  simp at nums_sum
  simp [show 99 * n = 3 * (33 * n) by ring] at nums_sum