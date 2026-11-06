import Mathlib

theorem number_theory_88152 (x : ℤ) : ¬ 169 ∣ x ^ 2 + 5 * x + 16 := by 
  intro h
  have h2 : x ^ 2 + 5 * x + 16 = 169 * ( (x ^ 2 + 5 * x + 16) / 169 ) := by 
    omega
  have h3 : x % 13 = 4 := by 
    have h4 : (x ^ 2 + 5 * x + 16) % 13 = 0 := by
      omega
    have : x % 13 = 0 ∨ x % 13 = 1 ∨ x % 13 = 2 ∨ x % 13 = 3 ∨ x % 13 = 4 ∨ x % 13 = 5 ∨ x % 13 = 6 ∨ x % 13 = 7 ∨ x % 13 = 8 ∨ x % 13 = 9 ∨ x % 13 = 10 ∨ x % 13 = 11 ∨ x % 13 = 12 := by 
      omega
    rcases this with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h4 <;> tauto
  have h5 : ∃ k : ℤ, x = 4 + 13 * k := by
    have : x % 13 = 4 := h3 
    refine' ⟨(x - 4) / 13, by omega⟩
  rcases h5 with ⟨k, hk⟩
  have h6 : (x ^ 2 + 5 * x + 16) % 169 = 0 := by 
    omega
  rw [hk] at h6 
  have eq1 : ( (4 + 13 * k) ^ 2 + 5 * (4 + 13 * k) + 16 ) % 169 = 52 % 169 := by
    ring_nf
    <;> omega
  omega