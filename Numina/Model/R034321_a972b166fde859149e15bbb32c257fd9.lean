import Mathlib

theorem algebra_94213 {n : ℕ} (hn : 4 ∣ n) :
    ∑ i ∈ Finset.Icc 1 (n + 1), (i * Complex.I ^ (i - 1)) = (n + 2 - n * Complex.I) / 2 := by
  rcases hn with ⟨k, hk⟩
  have eqn1 : n = 4 * k := by
    omega
  have eqn2 : n + 1 = 4 * k + 1 := by
    omega
  have h1 : ∀ (k : ℕ), ∑ i ∈ Finset.Icc 1 (4 * k + 1), (i * Complex.I ^ (i - 1)) = (4 * k + 2 - (4 * k) * Complex.I) / 2 := by
    intro k
    induction k with
    | zero =>
      simp [Finset.sum_singleton, pow_zero, mul_one, Complex.ext_iff]
      <;> norm_num
      <;> ring_nf <;> norm_num [Complex.I_sq, pow_add, pow_mul, pow_succ]
    | succ k ih =>
      rw [show 4 * (k + 1) + 1 = 4 * k + 5 by omega]
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [Finset.sum_Icc_succ_top (by linarith)]
      simp [ih]
      field_simp [Complex.ext_iff, pow_two, Complex.I_mul_I, pow_add, pow_mul, pow_succ]
      <;> ring_nf
      <;> simp [Complex.I_sq, Complex.I_im, Complex.I_re, pow_add, pow_mul, pow_succ, pow_zero]
      <;> ring_nf
      <;> norm_num
      <;> try { 
        ring_nf
        <;> norm_num [Complex.I_sq, pow_add, pow_mul, pow_succ]
        <;> simp [Complex.I_sq, pow_add, pow_mul, pow_succ]
      }
  rw [eqn2]
  specialize h1 k
  rw [h1]
  rw [eqn1]
  all_goals ring_nf <;> norm_num
  <;> simp [Complex.ext_iff, pow_two, Complex.I_mul_I, pow_add, pow_mul, pow_succ]
  <;> ring_nf
  <;> norm_num
  <;> try { 
    ring_nf 
    <;> norm_num [Complex.I_sq, pow_add, pow_mul, pow_succ]
    <;> simp [Complex.I_sq, pow_add, pow_mul, pow_succ]
  }
  all_goals try { 
    ring_nf
    <;> norm_num [Complex.I_sq, pow_add, pow_mul, pow_succ]
    <;> simp [Complex.I_sq, pow_add, pow_mul, pow_succ]
    <;> tauto 
  }