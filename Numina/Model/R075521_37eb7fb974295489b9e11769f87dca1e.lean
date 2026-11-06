import Mathlib

theorem number_theory_110400 : ¬∃ n : ℤ, 3 ∣ (n^2 + 1) := by
  rintro ⟨n, hn⟩
  have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h1 | h1 | h1)
  · -- Case n % 3 = 0
    have h2 : (n ^ 2 + 1) % 3 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    omega
  · -- Case n % 3 = 1
    have h2 : (n ^ 2 + 1) % 3 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    omega
  · -- Case n % 3 = 2
    have h2 : (n ^ 2 + 1) % 3 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    omega