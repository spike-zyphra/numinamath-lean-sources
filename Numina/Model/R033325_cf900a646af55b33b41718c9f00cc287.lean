import Mathlib

theorem number_theory_58697 (n : ℤ) : ¬ 81 ∣ n^3 - 9 * n + 27 := by
  intro h
  have h1 : (n^3 - 9 * n + 27) % 81 = 0 := by 
    omega
  have h2 : (n ^3 - 9 * n + 27) % 9 = 0 := by 
    omega
  have h7 : n^3 % 9 = 0 := by 
    have h8 : (n ^3 - 9 * n + 27) % 9 = 0 := h2
    have : (n ^3 - 9 * n + 27) % 9 = n^3 % 9 := by
      simp [Int.add_emod, Int.sub_emod, Int.mul_emod, Int.emod]
      all_goals try { omega }
    rw [this] at h8 
    omega 
  have h3 : n % 3 = 0 := by 
    have h8 : n^3 % 9 = 0 := h7
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h4 with (h4 | h4 | h4)
    · -- n % 3 = 0 
      omega
    · -- n % 3 = 1
      have h9 : n % 3 = 1 := h4
      have h10 : n^3 % 9 = 1 := by 
        have h4' : n % 3 = 1 := h9
        have h11 : n % 9 = 1 ∨ n % 9 = 4 ∨ n % 9 = 7 := by
          omega
        rcases h11 with (h | h | h)
        ·
          simp [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.emod] at *
        ·
          simp [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.emod] at *
        ·
          simp [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.emod] at *
      omega
    · -- n % 3 = 2 
      have h9 : n % 3 = 2 := h4
      have h10 : n^3 % 9 = 8 := by 
        have h4' : n % 3 = 2 := h9
        have h11 : n % 9 = 2 ∨ n % 9 = 5 ∨ n % 9 = 8 := by
          omega
        rcases h11 with (h | h | h)
        ·
          simp [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.emod] at *
        ·
          simp [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.emod] at *
        ·
          simp [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.emod] at *
      omega 
  -- Now we have n % 3 = 0, so n is a multiple of 3
  have h4 : ∃ k : ℤ, n = 3 * k := by
    refine' ⟨n / 3, by omega⟩
  rcases h4 with ⟨k,h5⟩
  have h6 : (n ^3 - 9 * n + 27) % 81 = 0 := h1
  rw [show n = 3 * k by linarith] at h6
  have h7 : ( (3 * k) ^3 - 9 * (3 * k) + 27 ) % 81 = 0 := h6 
  have h8 : ( (3 * k) ^3 - 9 * (3 * k) + 27 ) % 81 = (27 * (k^3 - k + 1)) % 81 := by
    ring_nf
  rw [h8] at h7 
  have h9 : (k^3 - k + 1) % 3 = 0 := by 
    omega
  have h10 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by 
    omega 
  rcases h10 with (h10 | h10 | h10)
  · -- k % 3 = 0 
    have h11 : k % 3 = 0 := h10 
    have h12 : (k^3 - k + 1) % 3 = 1 := by 
      simp [h11, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    omega 
  · -- k % 3 = 1 
    have h11 : k % 3 = 1 := h10 
    have h12 : (k^3 - k + 1) % 3 = 1 := by 
      simp [h11, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    omega 
  · -- k % 3 = 2 
    have h11 : k % 3 = 2 := h10 
    have h12 : (k^3 - k + 1) % 3 = 1 := by 
      simp [h11, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    omega