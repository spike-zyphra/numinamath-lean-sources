import Mathlib

theorem algebra_171983 (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : 2 * α ^ 2 - 2 * α * β + β ^ 2 = 0) :
    Complex.abs α = Complex.abs β ∨ Complex.abs α = Complex.abs (α - β) ∨
    Complex.abs β = Complex.abs (α - β) := by 
  have h4 : β ^ 2 - 2 * α * β + 2 * α ^ 2 = 0 := by 
    calc
      β ^ 2 - 2 * α * β + 2 * α ^ 2 = (2 * α^2 - 2 * α * β + β^2) := by ring
      _ = 0 := h

  have h5 : β ^ 2 - 2 * α * β + 2 * α ^ 2 = (β - α * (1 + Complex.I)) * (β - α * (1 - Complex.I)) := by
    ring_nf
    <;> simp [Complex.ext_iff, pow_two, Complex.I_mul_I]
    <;> ring
    <;> norm_num [Complex.I_sq]
    <;> ring

  rw [h5] at h4

  cases' (mul_eq_zero.mp h4) with h6 h7

  · -- case where β = α * (1 + i)
    have h8 : β = α * (1 + Complex.I) := by
      exact eq_of_sub_eq_zero h6
    have h9 : Complex.abs α = Complex.abs (α - β) := by
      have h10 : α - β = α * (-Complex.I) := by
        rw [h8]
        ring_nf
        <;> simp [Complex.ext_iff]
        all_goals ring
      rw [h10]
      have h11 : Complex.abs (α * (-Complex.I)) = Complex.abs α * Complex.abs (-Complex.I) := by 
        simp [Complex.abs, Complex.normSq]
        <;> ring
      rw [h11]
      have h12 : Complex.abs (-Complex.I) = 1 := by 
        simp [Complex.abs, Complex.normSq]
        <;> norm_num
        <;> simp [Complex.I_sq]
        <;> norm_num
      rw [h12]
      all_goals norm_num
    right
    left
    exact h9

  · -- case where β = α * (1 - i)
    have h8 : β = α * (1 - Complex.I) := by
      exact eq_of_sub_eq_zero h7
    have h9 : Complex.abs α = Complex.abs (α - β) := by
      have h10 : α - β = α * Complex.I := by
        rw [h8]
        ring_nf
        <;> simp [Complex.ext_iff]
        all_goals ring
      rw [h10]
      have h11 : Complex.abs (α * Complex.I) = Complex.abs α * Complex.abs Complex.I := by 
        simp [Complex.abs, Complex.normSq]
        <;> ring
      rw [h11]
      have h12 : Complex.abs Complex.I = 1 := by 
        simp [Complex.abs, Complex.normSq]
        <;> norm_num
        <;> simp [Complex.I_sq]
        <;> norm_num
      rw [h12]
      all_goals norm_num
    right
    left
    exact h9