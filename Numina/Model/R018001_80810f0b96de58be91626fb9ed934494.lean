import Mathlib

theorem number_theory_255968 (n : ℤ) : ¬ 121 ∣ n^2 + 3 * n + 5 ∧ ¬ 121 ∣ n^2 - 3 * n + 5 := by
  constructor
  · -- Assume $121$ divides $n^2 + 3 n + 5$, show $False$
    intro h
    have h1 : (n^2 + 3 * n + 5) % 121 = 0 := by
      omega
    have h2 : n % 11 = 4 := by
      have h1' : (n^2 + 3 * n + 5) % 11 = 0 := by
        omega
      have h16 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
        omega
      rcases h16 with (h | h | h | h | h | h | h | h | h | h | h)
      · -- n ≡ 0
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 1
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 2
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 3
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 4
        simp [h] at *
      · -- n ≡ 5
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 6
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 7
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 8
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 9
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
      · -- n ≡ 10
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at h1'
    have h3 : n % 121 = 4 ∨ n % 121 = 15 ∨ n % 121 = 26 ∨ n % 121 = 37 ∨ n % 121 = 48 ∨ n % 121 = 59 ∨ n % 121 = 70 ∨ n % 121 = 81 ∨ n % 121 = 92 ∨ n % 121 = 103 ∨ n % 121 = 114 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3)
    all_goals 
      simp [Int.add_emod, Int.mul_emod, pow_two, h3, Int.add_emod, Int.mul_emod] at h1
  · -- Assume $121$ divides $n^2 - 3 n + 5$, show $False$
    intro h
    have h1 : (n^2 - 3 * n + 5) % 121 = 0 := by 
      omega
    have h2 : n % 11 = 7 := by
      have h1' : (n^2 - 3 * n + 5) % 11 = 0 := by
        omega
      have h16 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
        omega
      rcases h16 with (h | h | h | h | h | h | h | h | h | h | h)
      · -- n ≡ 0
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 1
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 2
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 3
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 4
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 5
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 6
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 7
        simp [h] at *
      · -- n ≡ 8
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 9
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
      · -- n ≡ 10
        norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1'
    have h3 : n % 121 = 7 ∨ n % 121 = 18 ∨ n % 121 = 29 ∨ n % 121 = 40 ∨ n % 121 = 51 ∨ n % 121 = 62 ∨ n % 121 = 73 ∨ n % 121 = 84 ∨ n % 121 = 95 ∨ n % 121 = 106 ∨ n % 121 = 117 := by 
      omega
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3)
    all_goals 
      simp [Int.add_emod, Int.mul_emod, pow_two, h3, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1