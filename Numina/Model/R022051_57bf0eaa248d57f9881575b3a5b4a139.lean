import Mathlib

theorem number_theory_90199 (n : ℤ) : ¬ 81 ∣ n ^ 3 - 9 * n + 27 := by
  by_contra h
  have h1 : (n ^ 3 - 9 * n + 27) % 81 = 0 := by
    omega
  have h2 : n % 3 = 0 := by
    have h1 : (n ^ 3 - 9 * n + 27) % 3 = 0 := by
      omega
    have h3 : n ^ 3 % 3 = 0 := by
      omega
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h4 with (h5 | h5 | h5) <;> simp [h5, pow_succ, Int.add_emod, Int.mul_emod] at h3 ⊢ <;> omega
  have h3 : ∃ k : ℤ, n = 3 * k := by
    refine' ⟨n / 3, by omega⟩
  rcases h3 with ⟨k, hk⟩
  have eq1 : (n ^ 3 - 9 * n + 27) = 27 * (k ^ 3 - k + 1) := by
    rw [hk]
    ring
  have h4 : 27 * (k ^ 3 - k + 1) % 81 = 0 := by
    omega
  -- 81 divides 27(k^3 - k + 1) implies k^3 - k +1 divisible by 3
  have h5 : (k ^ 3 - k + 1) % 3 = 0 := by
    omega
  have h6 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
    omega
  rcases h6 with (h7 | h7 | h7) <;> simp [h7, pow_succ, Int.add_emod, Int.sub_emod, Int.mul_emod] at h5 ⊢ <;> omega