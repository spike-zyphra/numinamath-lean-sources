import Mathlib

theorem number_theory_288195 {a b c d : ℤ} (h₀ : b = a + d) (h₁ : c = b + d)
    (h₂ : d ≠ 0) (h₃ : a % d = 0) :
    6 * d^3 ∣ a * b * c := by 
  have h4 : b = a + d := h₀
  have h5 : c = a + 2 * d := by 
    rw [h₁, h4]
    ring
  have h6 : ∃ k, a = k * d := by
    have h7 : a % d = 0 := h₃
    have h8 : d ∣ a := by 
      exact Int.dvd_of_emod_eq_zero h7
    obtain ⟨k, hk⟩ := h8
    use k
    linarith
  rcases h6 with ⟨k, hk⟩
  have h7 : b = (k + 1) * d := by
    rw [h4]
    rw [hk]
    ring_nf
  have h8 : c = (k + 2) * d := by 
    rw [h5]
    rw [hk]
    ring_nf
  have h9 : a * b * c = k * (k + 1) * (k + 2) * d^3 := by
    rw [hk, h7, h8]
    ring
  rw [h9]
  have h11 : 6 ∣ k * (k + 1) * (k + 2) := by 
    have h10 : k * (k + 1) * (k + 2) % 6 = 0 := by
      have h11 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by
        omega
      rcases h11 with (h | h | h | h | h | h) <;> 
        simp [h, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have : k * (k + 1) * (k + 2) % 6 = 0 := h10
    have : k * (k + 1) * (k + 2) = k * (k + 1) * (k + 2) := by tauto
    have h15 : 6 ∣ k * (k + 1) * (k + 2) := by
      omega
    assumption
  have h12 : 6 * d ^ 3 ∣ k * (k + 1) * (k + 2) * d ^ 3 := by
    have h15 : 6 ∣ k * (k + 1) * (k + 2) := h11
    have h16 : 6 * d ^ 3 ∣ k * (k + 1) * (k + 2) * d ^ 3 := by 
      apply mul_dvd_mul_right
      exact h15
    assumption
  assumption