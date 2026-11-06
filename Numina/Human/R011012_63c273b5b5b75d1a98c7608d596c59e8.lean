import Mathlib

lemma find_solution {x y z : ℕ} (h₁ : x ^ (y ^ z - 1) = 5) (h₂ : y ^ (z ^ x - 1) = 1) (h₃ : z ^ (x ^ y - 1) = 1) : x = 5 ∧ y = 2 ∧ z = 1 := by
  rw [Nat.Prime.pow_eq_iff (by norm_num)] at h₁
  obtain ⟨hx, h₁⟩ := h₁
  rw [Nat.pred_eq_succ_iff] at h₁
  simp at h₁
  rw [Nat.Prime.pow_eq_iff (by norm_num)] at h₁
  obtain ⟨hy, hz⟩ := h₁
  omega

theorem number_theory_618551 : {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^(y^z) * y^(z^x) * z^(x^y) = 5 * x * y * z}.ncard = 3 := by
  -- The solution of the equation is (5, 2, 1), (1, 5, 2), and (2, 1, 5).
  suffices {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^(y^z) * y^(z^x) * z^(x^y) = 5 * x * y * z} = {(5, 2, 1), (1, 5, 2), (2, 1, 5)} by rw [this]; simp
  ext ⟨x, y, z⟩; simp
  constructor
  · -- ⟨x, y, z⟩ ∈ {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^(y^z) * y^(z^x) * z^(x^y) = 5 * x * y * z} → ⟨x, y, z⟩ ∈ {(5, 2, 1), (1, 5, 2), (2, 1, 5)}
    rintro ⟨hx₁, hy₁, hz₁, h₁⟩
    have h₂ : (x ^ (y ^ z - 1) * y ^ (z ^ x - 1) * z ^ (x ^ y - 1)) = 5 := by
      suffices (x ^ (y ^ z - 1) * y ^ (z ^ x - 1) * z ^ (x ^ y - 1)) * (x * y * z) = 5 * (x * y * z) by
        rw [Nat.mul_left_inj] at this
        exact this
        intro h₂
        simp at h₂
        obtain ((h₂ | h₂) | h₂) := h₂ <;> omega
      rw [show 5 * (x * y * z) = 5 * x * y * z by ring_nf, h₁.symm]
      ring_nf
      rw [mul_pow_sub_one (pow_ne_zero z (by linarith)) x, mul_assoc]
      rw [mul_pow_sub_one (pow_ne_zero y (by linarith)) z, mul_comm, mul_assoc]
      rw [mul_pow_sub_one (pow_ne_zero x (by linarith)) y]
      ring_nf

    -- so, we have x^(y^z - 1) * y^(z^x - 1) * z^(x^y - 1) = 5, and 5 = 1 * 1 * 5
    -- which means that x^(y^z - 1) = 1 or 5, y^(z^x - 1) = 1 or 5, z^(x^y - 1) = 1 or 5
    have h₃ : x ^ (y ^ z - 1) = 1 ∨ x ^ (y ^ z - 1) = 5 := by
      apply (Nat.dvd_prime (by norm_num)).mp
      rw [h₂.symm]
      suffices x ^ (y ^ z - 1) ∣ x ^ (y ^ z - 1) * y ^ (z ^ x - 1) by apply Dvd.dvd.mul_right this
      apply Nat.dvd_mul_right
    have h₄ : y ^ (z ^ x - 1) = 1 ∨ y ^ (z ^ x - 1) = 5 := by
      apply (Nat.dvd_prime (by norm_num)).mp
      rw [h₂.symm]
      suffices y ^ (z ^ x - 1) ∣ x ^ (y ^ z - 1) * y ^ (z ^ x - 1) by apply Dvd.dvd.mul_right this
      apply Nat.dvd_mul_left
    have h₅ : z ^ (x ^ y - 1) = 1 ∨ z ^ (x ^ y - 1) = 5 := by
      apply (Nat.dvd_prime (by norm_num)).mp
      rw [h₂.symm]
      apply Nat.dvd_mul_left
    obtain (h₃ | h₃) := h₃ <;> rw [h₃] at h₂
    · -- x ^ (y ^ z - 1) = 1
      apply Or.inr
      obtain (h₄ | h₄) := h₄ <;> rw [h₄] at h₂
      · -- y ^ (z ^ x - 1) = 1
        obtain (h₅ | h₅) := h₅ <;> rw [h₅] at h₂
        · -- z ^ (x ^ y - 1) = 1, contradiction
          omega
        · -- z ^ (x ^ y - 1) = 5
          apply Or.inr
          obtain ⟨hx, hy, hz⟩ := find_solution h₅ h₃ h₄
          omega
      · -- y ^ (z ^ x - 1) = 5
        obtain (h₅ | h₅) := h₅ <;> rw [h₅] at h₂
        · -- z ^ (x ^ y - 1) = 1
          apply Or.inl
          obtain ⟨hx, hy, hz⟩ := find_solution h₄ h₅ h₃
          omega
        · -- z ^ (x ^ y - 1) = 5, contradiction
          omega
    · -- x ^ (y ^ z - 1) = 5, which means that y ^ (z ^ x - 1) = 1 and z ^ (x ^ y - 1) = 1
      obtain (h₄ | h₄) := h₄ <;> rw [h₄] at h₂
      · -- y ^ (z ^ x - 1) = 1
        obtain (h₅ | h₅) := h₅ <;> rw [h₅] at h₂
        · -- z ^ (x ^ y - 1) = 1
          apply Or.inl
          obtain ⟨hx, hy, hz⟩ := find_solution h₃ h₄ h₅
          omega
        · -- z ^ (x ^ y - 1) = 5, contradiction
          omega
      · -- y ^ (z ^ x - 1) = 5, contradiction
        omega
  · -- ⟨x, y, z⟩ ∈ {(5, 2, 1), (1, 5, 2), (2, 1, 5)} → ⟨x, y, z⟩ ∈ {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x^(y^z) * y^(z^x) * z^(x^y) = 5 * x * y * z}
    rintro (⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩)
    all_goals {
      rw [hx, hy, hz]
      norm_num
    }
