import Mathlib

open Real

theorem algebra_263409 (a : ℕ → ℝ) (ha : ∀ n, a n = 1 + 3 * n) :
    ⌈∑ i ∈ Finset.range 1579, 1 / (sqrt (a i) + sqrt (a (i + 1)))⌉ = 23 := by
  have h1 : ∀ (i : ℕ), a i = 1 + 3 * (i : ℝ) := by
    intro i
    specialize ha i
    simpa using ha
  have h2 : ∀ i : ℕ, 1 / (sqrt (a i) + sqrt (a (i + 1))) = (sqrt (a (i + 1)) - sqrt (a i)) / 3 := by
    intro i
    have h3 : a i = 1 + 3 * (i : ℝ) := h1 i
    have h7 : a (i + 1) = 1 + 3 * ((i : ℝ) + 1) := by
      have h5 : a (i + 1) = 1 + 3 * ((i + 1 : ℕ) : ℝ) := h1 (i + 1)
      simp at h5 ⊢
      <;> linarith
    have h8 : a (i + 1) - a i = 3 := by
      rw [h7, h3]
      ring
    have h9 : sqrt (a i) ≥ 0 := Real.sqrt_nonneg (a i)
    have h10 : sqrt (a (i + 1)) ≥ 0 := Real.sqrt_nonneg (a (i + 1))
    have h11 : sqrt (a i) ^ 2 = a i := Real.sq_sqrt (show (0 : ℝ) ≤ a i by
      rw [h3]
      nlinarith
    )
    have h12 : sqrt (a (i + 1)) ^ 2 = a (i + 1) := Real.sq_sqrt (show (0 : ℝ) ≤ (a (i + 1) : ℝ) by
      rw [h7]
      nlinarith
    )
    field_simp [(show sqrt (a i) + sqrt (a (i + 1)) ≠ 0 by
      have h13 : sqrt (a i) ≥ 0 := h9
      have h14 : sqrt (a (i + 1)) ≥ 0 := h10
      by_contra h
      have h19 : sqrt (a i) + sqrt (a (i + 1)) = 0 := by linarith
      have h20 : sqrt (a i) = 0 := by
        nlinarith [h19, h13, h14]
      have h21 : sqrt (a (i + 1)) = 0 := by
        nlinarith [h19, h13, h14]
      have h39 : a i = 0 := by
        rw [Real.sqrt_eq_zero (show (0 : ℝ) ≤ a i by
          rw [h3]
          nlinarith
        )] at h20
        linarith
      have h40 : a i > 0 := by
        rw [h3]
        nlinarith
      linarith
    )]
    <;> nlinarith [Real.sqrt_nonneg (a i), Real.sqrt_nonneg (a (i + 1)),
        Real.sq_sqrt (show (0 : ℝ) ≤ a i by
          rw [h3]
          nlinarith
        ), Real.sq_sqrt (show (0 : ℝ) ≤ (a (i + 1)) by
          rw [h7]
          nlinarith
        ), h8, sq_nonneg (sqrt (a (i + 1)) - sqrt (a i))
      ]
  have h3 : ∑ i ∈ Finset.range 1579, 1 / (sqrt (a i) + sqrt (a (i + 1))) = (Real.sqrt (a 1579) - Real.sqrt (a 0)) / 3 := by
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    have h4 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (sqrt (a (i + 1)) - sqrt (a i)) / 3 = (sqrt (a n) - sqrt (a 0)) / 3 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp
        <;> ring
    specialize h4 1579
    linarith [h4]
  rw [h3]
  have h5 : a 0 = 1 := by
    specialize ha 0
    norm_num at ha ⊢
    linarith
  have h6 : a 1579 = (4738 : ℝ) := by
    have h68 : a 1579 = 1 + 3 * (1579 : ℕ) := h1 1579
    norm_num at h68 ⊢
    linarith
  rw [h5, h6]
  have h7 : 67 ^ 2 < (4738 : ℝ) := by
    norm_num
  have h8 : (67 : ℝ) < Real.sqrt 4738 := by
    nlinarith [Real.sqrt_nonneg (4738 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (4738 : ℝ) by norm_num), Real.sqrt_nonneg (4738 : ℝ)]
  have h9 : (Real.sqrt 4738 - 1) / 3 > (22 : ℝ) := by
    nlinarith [h8, Real.sqrt_nonneg (4738 : ℝ)]
  have h10 : Real.sqrt 4738 < (69 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (4738 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (4738 : ℝ) by norm_num), Real.sqrt_nonneg (4738 : ℝ)]
  have h11 : (Real.sqrt 4738 - 1) / 3 < (23 : ℝ) := by
    nlinarith [h10, Real.sqrt_nonneg (4738 : ℝ)]
  rw [Int.ceil_eq_iff]
  constructor <;> (try norm_num) <;> try nlinarith