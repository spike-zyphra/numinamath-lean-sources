import Mathlib

theorem algebra_12667 {a r : ℝ} (hr : r ≠ 0) (h1 : ∑ i ∈ Finset.range 2014, a * r ^ i = 200)
    (h2 : ∑ i ∈ Finset.range 4028, a * r ^ i = 380) :
    ∑ i ∈ Finset.range 6042, a * r ^ i = 542 := by

  have h3 : ∑ i in Finset.range 4028, a * r ^ i = ∑ i in Finset.range 2014, a * r ^ i + r ^ 2014 * ∑ i in Finset.range 2014, a * r ^ i := by 
    rw [show 4028 = 2014 + 2014 by norm_num]
    rw [Finset.sum_range_add]
    have h4 : ∀ i : ℕ, a * r ^ (2014 + i) = r ^ 2014 * (a * r ^ i) := by
      intro i
      ring_nf
      <;> simp [pow_add]
      <;> ring_nf
      <;> simp [pow_add]
      <;> ring_nf
    simp_rw [h4]
    rw [Finset.mul_sum]
    <;> ring_nf
    <;> simp [pow_add]

  have hr2014 : r ^ 2014 = 0.9 := by
    have h5 : r ^ 2014 * (∑ i in Finset.range 2014, a * r ^ i) = (380 - 200) := by
      nlinarith [h1, h2, h3]
    rw [h1] at h5
    have h6 : r ^ 2014 = (380 - 200) / 200 := by
      field_simp at h5 ⊢
      <;> nlinarith
      <;> field_simp
    norm_num at h5 h6 ⊢
    nlinarith

  have h4 : ∑ i in Finset.range 6042, a * r ^ i = ∑ i in Finset.range 4028, a * r ^ i + r ^ 4028 * ∑ i in Finset.range 2014, a * r ^ i := by
    rw [show 6042 = 4028 + 2014 by norm_num]
    rw [Finset.sum_range_add]
    have h5 : ∀ i : ℕ, a * r ^ (4028 + i) = r ^ 4028 * (a * r ^ i) := by
      intro i
      ring_nf
      <;> simp [pow_add]
      <;> ring_nf
      <;> simp [pow_add]
      <;> ring_nf
      <;> simp [pow_add]
      <;> ring_nf
      <;> simp [pow_add]
      <;> ring_nf
    simp_rw [h5]
    rw [Finset.mul_sum]
    <;> ring_nf <;> simp [pow_add]

  have hr4028 : r ^ 4028 = (r ^ 2014) ^ 2 := by
    ring_nf
    <;> simp [pow_mul]
    <;> ring_nf
    <;> simp [pow_mul]

  have hr4028_eq : r ^ 4028 = 0.81 := by
    rw [hr4028, hr2014]
    norm_num
  
  rw [h4]
  rw [h2, h1]
  rw [hr4028_eq]
  norm_num