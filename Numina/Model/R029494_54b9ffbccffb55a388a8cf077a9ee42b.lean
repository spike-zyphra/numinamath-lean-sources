import Mathlib

theorem number_theory_254712 (a b : ℤ) (ha : Even a) (hb : Odd b)
    (h : ∃ n, n^2 = a^2 + b^2) : 4 ∣ a := by 
  rcases h with ⟨n, hn⟩
  rcases ha with ⟨k, hk⟩
  rcases hb with ⟨m, hm⟩
  have eq1 : n ^ 2 = (2 * k) ^ 2 + (2 * m + 1) ^ 2 := by
    rw [hk, hm] at hn
    linarith
  have eq3 : n ^ 2 % 4 = 1 := by
    have eq4 : (2 * k) ^ 2 + (2 * m + 1) ^ 2 = (n ^ 2) := by linarith [eq1]
    have eq5 : ((2 * k) ^ 2 + (2 * m + 1) ^ 2) % 4 = 1 := by 
      have eq6 : ((2 * k) ^ 2) % 4 = 0 := by
        have h7 : (2 * k) ^ 2 = 4 * (k ^ 2) := by ring
        rw [h7]
        omega
      have eq7 : ((2 * m + 1) ^ 2) % 4 = 1 := by
        have eq8 : (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 := by 
          omega
        rcases eq8 with (h | h)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      omega
    omega 
  have h6 : n % 2 = 1 := by 
    by_contra h7
    push_neg at h7
    have h8 : n % 2 = 0 := by omega
    have h9 : (n ^ 2) % 4 = 0 := by 
      have h10 : (n % 4 = 0 ∨ n % 4 = 2) := by 
        omega 
      rcases h10 with (h10 | h10)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h10, Int.sub_emod]
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h10, Int.sub_emod]
    omega 
  -- Show that n^2 modulo 8 is 1
  have eq5 : (n ^ 2) % 8 = 1 := by
    have eq4 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      omega
    rcases eq4 with (h | h | h | h)
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
    · 
      simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
  have eq6 : ((2 * k) ^ 2 + (2 * m + 1) ^ 2) % 8 = 1 := by 
    have eq7 : (n ^ 2) % 8 = 1 := eq5
    have eq8 : ( (2 * k) ^ 2 + (2 * m + 1) ^ 2 ) % 8 = (n ^ 2) % 8 := by 
      omega
    linarith
  have hk2 : k % 2 = 0 := by 
    by_contra h
    push_neg at h
    have eq8 : k % 2 = 1 := by 
      omega
    have eq9 : ((2 * k) ^ 2 + (2 * m + 1) ^ 2) % 8 = 5 := by
      have eq10 : k % 2 = 1 := eq8
      have eq11 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by
        omega 
      rcases eq11 with (h1 | h1 | h1 | h1)
      all_goals
        have eq12 : ((2 * k) ^ 2 + (2 * m + 1) ^ 2) % 8 = 5 := by
          have eq13 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by 
            omega 
          have eq14 : (k : ℤ) % 2 = 1 := by 
            omega 
          have eq15 : (2 * k) ^ 2 % 8 = 4 := by
            rcases eq13 with (h1 | h1 | h1 | h1) <;> simp [Int.add_emod, Int.mul_emod, h1, pow_two]
          have eq16 : (2 * m + 1) ^ 2 % 8 = 1 := by
            have eq17 : (2 * m + 1 : ℤ ) % 2 = 1 := by 
              omega 
            have eq18 : (2 * m + 1 : ℤ ) % 8 = 1 ∨ (2 * m + 1 : ℤ ) % 8 = 3 ∨ (2 * m + 1 : ℤ ) % 8 = 5 ∨ (2 * m + 1 : ℤ ) % 8 = 7 := by 
              omega 
            rcases eq18 with (h1 | h1 | h1 | h1) <;> simp [Int.add_emod, Int.mul_emod, h1, pow_two] 
          omega 
        linarith 
    omega
  have ha2 : a = 4 * (k / 2) := by 
    have hk0 : k % 2 = 0 := hk2
    have h0 : ∃ t, k = 2 * t := by 
      refine' ⟨k / 2, by omega⟩
    rcases h0 with ⟨t, ht⟩
    omega
  rw [ha2]
  all_goals 
    omega