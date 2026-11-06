import Mathlib

theorem algebra_13556 (x : ℂ) (hx : x ≠ 0 ∧ x - x⁻¹ = .I * √2) :
    x ^ 2187 - x⁻¹ ^ 2187 = .I * √2 := by
  rcases hx with ⟨hx1, hx2⟩
  have eq2 : ∀ (n : ℕ), x ^ (3 ^ n) - x⁻¹ ^ (3 ^ n) = .I * √2 := by
    intro n 
    induction n with
    | zero =>
      simp [hx2]
    | succ n ih =>
      have eq3 : x ^ (3 ^ (n + 1 : ℕ)) - x⁻¹ ^ (3 ^ (n + 1 : ℕ)) = (x ^ (3 ^ n)) ^ 3 - (x⁻¹ ^ (3 ^ n)) ^ 3 := by
        ring_nf
      have eq4 : (x ^ (3 ^ n)) ^ 3 - (x⁻¹ ^ (3 ^ n)) ^ 3 = ((x ^ (3 ^ n) - x⁻¹ ^ (3 ^ n) ) ) ^ 3 + 3 * (x ^ (3 ^ n) - x⁻¹ ^ (3 ^ n) ) := by 
        field_simp [hx1] at *
        ring
      rw [eq3, eq4, ih]
      field_simp at *
      simp [pow_three] 
      <;> ring_nf <;> simp [Complex.ext_iff, pow_three, pow_two, mul_add, mul_assoc] 
      <;> ring_nf
      <;> norm_num [Complex.ext_iff, pow_two, pow_three]
  have h1 : x ^ 2187 - x⁻¹ ^ 2187 = .I * √2 := by 
    specialize eq2 7 
    norm_num at eq2 ⊢ 
    exact_mod_cast eq2
  exact h1