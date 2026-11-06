import Mathlib

theorem algebra_314719 (x : ℤ) : ¬(169 ∣ x^2 + 5 * x + 16) := by
  intro h
  have h1 : (x^2 + 5 * x + 16) % 169 = 0 := by
    omega
  have h2 : (x^2 + 5 * x + 16) % 13 = 0 := by
    omega
  have h3 : x % 13 = 4 := by
    have h2' : (x^2 + 5 * x + 16) % 13 = 0 := h2
    have : x % 13 = 0 ∨ x % 13 = 1 ∨ x % 13 = 2 ∨ x % 13 = 3 ∨ x % 13 = 4 ∨ x % 13 = 5 ∨ x % 13 = 6 ∨ x % 13 = 7 ∨ x % 13 = 8 ∨ x % 13 = 9 ∨ x % 13 = 10 ∨ x % 13 = 11 ∨ x % 13 = 12 := by
      omega
    rcases this with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h2' <;> tauto
  have h4 : ∃ t : ℤ, x = 13 * t + 4 := by
    refine' ⟨(x - 4) / 13, by 
      omega
    ⟩
  rcases h4 with ⟨t, ht⟩
  rw [ht] at h1
  ring_nf at h1 
  omega