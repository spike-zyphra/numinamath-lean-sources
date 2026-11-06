import Mathlib

theorem algebra_214332 {u v w : ℂ} (hu : u = -1 + Complex.I * Real.sqrt 3)
    (hv : v = -1 - Complex.I * Real.sqrt 3) (hw : w = 2) (n : ℕ) (hn : ¬ 3 ∣ n) :
    u^n + v^n + w^n = 0 := by
  have h1 : u^3 = 8 := by
    rw [hu]
    simp [pow_three, Complex.ext_iff, mul_add, mul_comm, Complex.I_mul_I, mul_assoc]
    ring_nf
    <;> norm_num [Real.sqrt_sq]
    <;> ring_nf <;> norm_num [Real.sqrt_sq]

  have h2 : v^3 = 8 := by
    rw [hv]
    simp [pow_three, Complex.ext_iff, mul_add, mul_comm, Complex.I_mul_I, mul_assoc]
    ring_nf
    <;> norm_num [Real.sqrt_sq]
    <;> ring_nf <;> norm_num [Real.sqrt_sq]

  have h3 : n % 3 = 1 ∨ n % 3 = 2 := by 
    omega

  rcases h3 with (h | h)
  · -- if n ≡ 1 [MOD 3]
    have h4 : n % 3 = 1 := h
    have h5 : ∃ k : ℕ, n = 3 * k + 1 := by 
      refine' ⟨(n - 1) / 3, by omega⟩
    rcases h5 with ⟨k, hk⟩
    rw [hk]
    have eq1 : u ^ (3 * k + 1) = (8 : ℂ) ^ k * u := by
      have h8 : u^3 = 8 := h1
      have eq9 : u ^ (3 * k + 1) = (u ^ (3 * k)) * u := by
        ring_nf
      rw [eq9]
      have eq10 : u ^ (3 * k) = (u ^ 3) ^ k := by
        rw [pow_mul]
      rw [eq10, h8]
      all_goals norm_num
    have eq2 : v ^ (3 * k + 1) = (8 : ℂ) ^ k * v := by
      have h8 : v^3 = 8 := h2
      have eq9 : v ^ (3 * k + 1) = (v ^ (3 * k)) * v := by
        ring_nf
      rw [eq9]
      have eq10 : v ^ (3 * k) = (v ^ 3) ^ k := by
        rw [pow_mul]
      rw [eq10, h8]
      all_goals norm_num
    rw [eq1, eq2]
    rw [hw]
    simp [pow_mul, pow_add, hu, hv]
    ring_nf
    <;> norm_num [Real.sqrt_sq, pow_two, pow_zero, Complex.ext_iff, Complex.I_mul_I]
    <;> ring_nf <;> norm_num [Real.sqrt_sq]
    all_goals ring
  · -- if n ≡ 2 [MOD 3]
    have h4 : n % 3 = 2 := h
    have h5 : ∃ k : ℕ, n = 3 * k + 2 := by 
      refine' ⟨(n - 2) / 3, by omega⟩
    rcases h5 with ⟨k, hk⟩
    rw [hk]
    have eq1 : u ^ (3 * k + 2) = (8 : ℂ) ^ k * (u ^ 2) := by
      have h8 : u^3 = 8 := h1
      have eq9 : u ^ (3 * k + 2) = (u ^ (3 * k)) * u ^ 2 := by
        ring_nf
      rw [eq9]
      have eq10 : u ^ (3 * k) = (u ^ 3) ^ k := by
        rw [pow_mul]
      rw [eq10, h8]
      all_goals norm_num
    have eq2 : v ^ (3 * k + 2) = (8 : ℂ) ^ k * (v ^ 2) := by
      have h8 : v^3 = 8 := h2
      have eq9 : v ^ (3 * k + 2) = (v ^ (3 * k)) * v ^ 2 := by
        ring_nf
      rw [eq9]
      have eq10 : v ^ (3 * k) = (v ^ 3) ^ k := by
        rw [pow_mul]
      rw [eq10, h8]
      all_goals norm_num
    have eq5 : u ^ 2 = (-2 - 2 * Complex.I * Real.sqrt 3) := by
      rw [hu]
      simp [pow_two, Complex.ext_iff, Complex.I_mul_I, mul_pow, pow_two]
      ring_nf
      <;> norm_num [Real.sqrt_sq]
      <;> ring_nf <;> norm_num [Real.sqrt_sq]
      <;> ring
    have eq6 : v ^ 2 = (-2 + 2 * Complex.I * Real.sqrt 3) := by
      rw [hv]
      simp [pow_two, Complex.ext_iff, Complex.I_mul_I, mul_pow, pow_two]
      ring_nf
      <;> norm_num [Real.sqrt_sq]
      <;> ring_nf <;> norm_num [Real.sqrt_sq]
      <;> ring
    rw [eq1, eq2, hw, eq5, eq6]
    simp [pow_add, pow_mul, hw]
    ring_nf
    <;> norm_num [Real.sqrt_sq, pow_two, pow_zero, Complex.ext_iff, Complex.I_mul_I]
    <;> ring_nf <;> norm_num [Real.sqrt_sq]
    all_goals ring