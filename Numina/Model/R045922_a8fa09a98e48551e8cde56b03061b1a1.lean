import Mathlib

def A (x : ℕ) := ∃ n, x = 2 * n
def B (x : ℕ) := ∃ n, x = 3 * n
def C (x : ℕ) := ∃ n, x = n ^ 2

theorem number_theory_324731 :
    {x | A x ∧ B x ∧ C x} = {x | ∃ n, x = 36 * n ^ 2} := by
  ext x
  simp [A, B, C]
  constructor
  · -- Assume x in the left side, need to show in right side
    rintro ⟨⟨n, h₁⟩, ⟨m, h₂⟩, ⟨k, h₃⟩⟩
    have h4 : k ^ 2 = 2 * n := by linarith
    have h5 : k ^ 2 = 3 * m := by linarith
    have h6 : k ^ 2 % 2 = 0 := by 
      omega
    have h7 : k ^ 2 % 3 = 0 := by 
      omega
    have h8 : k % 2 = 0 := by
      by_contra h
      push_neg at h
      have h9 : k % 2 = 1 := by omega
      have h10 : (k ^ 2) % 2 = 1 := by
        simp [Nat.pow_mod, h9]
      omega
    have h9 : k % 3 = 0 := by 
      by_contra h
      push_neg at h
      have h10 : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h10 with (h10 | h10)
      · -- k ≡ 1 (mod 3)
        have h11 : (k ^ 2) % 3 = 1 := by
          simp [Nat.pow_mod, h10]
        omega
      · -- k ≡ 2 (mod 3)
        have h12 : (k ^ 2) % 3 = 1 := by
          simp [Nat.pow_mod, h10]
        omega
    have h10 : ∃ t, k = 6 * t := by
      have h11 : k % 2 = 0 := h8
      have h12 : k % 3 = 0 := h9
      have h13 : k % 6 = 0 := by
        omega
      refine ⟨k / 6, by omega⟩
    rcases h10 with ⟨t, ht⟩
    use t
    rw [ht] at h₃
    nlinarith
  · -- Assume x in the right side, need to show in left side
    rintro ⟨t, ht⟩
    refine ⟨⟨18 * t ^ 2, by linarith⟩, ⟨12 * t ^ 2, by linarith⟩, ⟨6 * t, by nlinarith⟩⟩