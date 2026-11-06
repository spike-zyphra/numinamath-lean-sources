import Mathlib

theorem number_theory_176720 {n : ℤ} (hn : ∃ k, n = k^2) (hdiv : ¬ 9 ∣ n) :
    n % 3 = 1 := by
  rcases hn with ⟨k, rfl⟩
  by_contra h
  push_neg at h
  have h1 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by 
    omega
  rcases h1 with (h1 | h1 | h1)
  · 
    -- Let's prove that k ≡ 0 (mod 3) implies (k^2) divisible by 9
    -- Therefore 9 | k^2 contradicts ¬ 9 ∣ k^2.
    have h2 : (k ^ 2) % 9 = 0 := by
      have h4 : k % 9 = 0 ∨ k % 9 = 3 ∨ k % 9 = 6 := by
        omega
      rcases h4 with (h4 | h4 | h4)
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
        <;> omega
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
        <;> omega
      · 
        simp [pow_two, Int.add_emod, Int.mul_emod, h4]
        <;> omega
    have h5 : 9 ∣ (k ^ 2) := by
      omega
    exact hdiv h5
  · 
    -- Let's compute k ≡ 1 (mod 3) ⇒ k^2 ≡ 1 (mod 3)
    -- Therefore the hypothesis of contradiction (k^2 ≡ 0 or 2 mod 3) is exfalso.
    have h5 : (k ^ 2) % 3 = 1 := by
      have h8 : k % 3 = 1 := h1
      have h9 : k ^ 2 % 3 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h8]
        <;> omega
      omega
    omega
  · 
    -- Let's compute k ≡ 2 (mod 3) ⇒ k^2 ≡ 1 (mod 3)
    -- Therefore the hypothesis of contradiction (k^2 ≡ 0 or 2 mod 3) is exfalso.
    have h5 : (k ^ 2) % 3 = 1 := by
      have h8 : k % 3 = 2 := h1
      have h9 : k ^ 2 % 3 = 1 := by
        simp [pow_two, Int.add_emod, Int.mul_emod, h8]
        <;> omega
      omega
    omega