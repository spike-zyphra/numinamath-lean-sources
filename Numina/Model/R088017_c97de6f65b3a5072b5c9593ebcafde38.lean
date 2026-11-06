import Mathlib

theorem algebra_18846 {f g : ℝ → ℝ}
    (hf : f = fun x => x^3 - 49 * x^2 + 623 * x - 2015)
    (hg : g = fun x => f (x + 5)) :
    ∑ᶠ x ∈ g⁻¹' {0}, x = 34 := by
  have g_def : ∀ x, g x = f (x + 5) := by
    intro x
    rw [hg]
  have f_def : ∀ x, f x = x^3 - 49 * x^2 + 623 * x - 2015 := by
    intro x
    rw [hf]
  -- Simplify g(x) to cubic polynomial
  have eq1 : ∀ (x : ℝ), g x = 0 ↔ x ^ 3 - 34 * x ^ 2 + 208 * x = 0 := by
    intro x
    have eq2 : g x = f (x + 5) := by simp [g_def]
    rw [eq2]
    have eq3 : f (x + 5) = (x + 5) ^ 3 - 49 * (x + 5) ^ 2 + 623 * (x + 5) - 2015 := by
      simp [f_def]
      <;> ring_nf <;> norm_num
      <;> ring
    rw [eq3]
    constructor
    · -- Assume f(x + 5) = 0, sove equation
      intro h_eq
      ring_nf at h_eq ⊢
      nlinarith [sq_nonneg (x), sq_nonneg (x - 8), sq_nonneg (x - 26)]
    · -- Assume x^3 - 34x^2 + 208x = 0, prove f(x + 5) = 0
      intro h_eq
      ring_nf at h_eq ⊢
      nlinarith [sq_nonneg (x), sq_nonneg (x - 8), sq_nonneg (x - 26)]
  -- Determine the zero set of g
  have h_zeroSet : g⁻¹' {0} = ({0, 8, 26} : Set ℝ) := by
    ext x
    simp [eq1]
    constructor
    · -- Forward direction
      intro h
      have h_eq : x ^ 3 - 34 * x ^ 2 + 208 * x = 0 := h
      have h_zeroes : x = (0 : ℝ) ∨ x = (8 : ℝ) ∨ x = (26 : ℝ) := by
        have : x * (x - 8) * (x - 26) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp this) with h1 h2
        · cases' (mul_eq_zero.mp h1) with h_eq0 h_eq8
          · left
            linarith
          · right
            left
            linarith
        · right
          right
          linarith
      tauto
    · -- Backward direction
      rintro (h | h | h)
      · -- x = 0
        rw [h]
        norm_num
        <;> ring
      · -- x = 8
        rw [h]
        norm_num
        <;> ring
      · -- x = 26
        rw [h]
        norm_num
        <;> ring
  rw [h_zeroSet]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> norm_num
  <;> ring