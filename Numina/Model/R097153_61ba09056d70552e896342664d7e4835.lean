import Mathlib

theorem number_theory_106692 (n : ℤ) : ¬ 7 ∣ (n ^ 2 + 1) := by
  have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1)
  · -- Case n % 7 = 0
    have h2 : (n ^ 2 + 1) % 7 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3
  · -- Case n % 7 = 1
    have h2 : (n ^ 2 + 1) % 7 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3
  · -- Case n % 7 = 2
    have h2 : (n ^ 2 + 1) % 7 = 5 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3
  · -- Case n % 7 = 3
    have h2 : (n ^ 2 + 1) % 7 = 3 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3
  · -- Case n % 7 = 4
    have h2 : (n ^ 2 + 1) % 7 = 3 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3
  · -- Case n % 7 = 5
    have h2 : (n ^ 2 + 1) % 7 = 5 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3
  · -- Case n % 7 = 6
    have h2 : (n ^ 2 + 1) % 7 = 2 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, Int.ofNat, h1]
      all_goals omega
    have h3 : ¬ 7 ∣ (n ^ 2 + 1) := by
      intro h
      have h4 : (n ^ 2 + 1) % 7 = 0 := by
        omega
      omega
    exact h3