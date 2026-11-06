import Mathlib

theorem algebra_119893 (a b c d e : ℕ) (h₀ : (a + b + c + d + e) / 5 = 24)
    (h₁ : a / (b + c) = 2 ∧ a % (b + c) = 1) (h₂ : b / (c + d) = 2 ∧ b % (c + d) = 1)
    (h₃ : c / (d + e) = 2 ∧ c % (d + e) = 1) (h₄ : d = e - 1) :
    a = 77 ∧ b = 27 ∧ c = 11 ∧ d = 2 ∧ e = 3 := by
  have h5 : a + b + c + d + e ≥ 120 := by
    omega
  have h6 : a + b + c + d + e ≤ 124 := by
    omega
  have h7 : a = 2 * (b + c) + 1 := by
    have h := h₁.1
    have h' := h₁.2
    calc
      a = (b + c) * (a / (b + c)) + a % (b + c) := by
        rw [Nat.div_add_mod a (b + c)]
      _ = (b + c) * 2 + 1 := by
        simp [h, h']
      _ = 2 * (b + c) + 1 := by
        ring
  have h8 : b = 2 * (c + d) + 1 := by
    have h := h₂.1
    have h' := h₂.2
    calc
      b = (c + d) * (b / (c + d)) + b % (c + d) := by
        rw [Nat.div_add_mod b (c + d)]
      _ = (c + d) * 2 + 1 := by
        simp [h, h']
      _ = 2 * (c + d) + 1 := by
        ring
  have h9 : c = 2 * (d + e) + 1 := by
    have h := h₃.1
    have h' := h₃.2
    calc
      c = (d + e) * (c / (d + e)) + c % (d + e) := by
        rw [Nat.div_add_mod c (d + e)]
      _ = (d + e) * 2 + 1 := by
        simp [h, h']
      _ = 2 * (d + e) + 1 := by
        ring
  have h10 : d = e - 1 := h₄
  have h11 : c = 4 * e - 1 := by
    rw [h10] at h9
    omega
  have h12 : b = 10 * e - 3 := by
    rw [h11] at h8
    rw [h10] at h8
    omega
  have h13 : a = 28 * e - 7 := by
    rw [h12] at h7
    rw [h11] at h7
    omega
  have h14 : e = 3 := by
    have h15 : a + b + c + d + e = 120 := by
      omega
    omega
  have h15 : d = 2 := by
    omega
  have h16 : c = 11 := by
    omega
  have h17 : b = 27 := by
    omega
  have h18 : a = 77 := by
    omega
  exact ⟨h18, h17, h16, h15, h14⟩