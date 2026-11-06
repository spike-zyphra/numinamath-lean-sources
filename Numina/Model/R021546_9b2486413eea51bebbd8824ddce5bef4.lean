import Mathlib

theorem number_theory_212048 (a : ℤ) (h : ∃ x y, 3 * a = x ^ 2 + 2 * y ^ 2) :
    ∃ x y, a = x ^ 2 + 2 * y ^ 2 := by
  rcases h with ⟨x, y, h_eq⟩
  have eq1 : (x ^ 2 + 2 * y ^ 2) % 3 = 0 := by
    omega
  have eq2 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by
    omega 
  have eq3 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
    omega 
  have h5 : (x % 3 = y % 3) ∨ (x % 3 = (3 - (y % 3)) % 3) := by
    rcases eq2 with (h2x | h2x | h2x) <;> rcases eq3 with (h2y | h2y | h2y) <;> simp [h2x, h2y, 
      pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at eq1 ⊢ 
      <;> omega
  rcases h5 with h5 | h5
  · -- Case x ≡ y (mod 3)
    have h6 : x % 3 = y % 3 := h5
    have h7 : ∃ k, x = y + 3 * k := by
      have h8 : x % 3 = y % 3 := h6
      have h9 : (x - y) % 3 = 0 := by 
        omega
      refine ⟨(x - y) / 3, ?_⟩
      omega
    rcases h7 with ⟨k, hk⟩
    use y + k, k
    have eq3 : 3 * a = x ^ 2 + 2 * y ^ 2 := h_eq
    rw [show x = y + 3 * k by linarith [hk]] at eq3
    nlinarith [sq_nonneg (y + k), sq_nonneg (k), sq_nonneg ((y + 3 * k) - y - 3 * k)]
  · -- Case x ≡ -y (mod 3)
    have h6 : x % 3 = (3 - (y % 3)) % 3 := h5
    have h7 : ∃ k, x = -y + 3 * k := by
      have eq1' : x % 3 = (3 - (y % 3)) % 3 := h6
      have h8 : (x + y) % 3 = 0 := by 
        omega
      refine ⟨(x + y) / 3, ?_⟩
      omega
    rcases h7 with ⟨k, hk⟩
    use y - k, k
    have eq3 : 3 * a = x ^ 2 + 2 * y ^ 2 := h_eq
    rw [show x = -y + 3 * k by linarith [hk]] at eq3
    nlinarith [sq_nonneg (y - k), sq_nonneg (k), sq_nonneg (x + y - 3 * k)]