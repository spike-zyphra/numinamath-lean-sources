import Mathlib

open Real

/-show that cos(56∘)cos(2*56∘)...cos(2^23*56∘) = 1/2^24 -/
theorem algebra_10031: ∏ k ∈ Finset.range 24, cos ((2^k) * (56 * π / 180)) = 1 / 2^24 := by
  -- Convert degrees to radians
  let θ := 56 * π / 180

  -- Firstly, we need to show that sin(θ) is not zero --
  have h_sin_ne: sin θ ≠ 0 := by
    by_contra! no
    simp [θ] at no
    rw [Real.sin_eq_zero_iff_of_lt_of_lt] at no
    absurd no
    norm_num
    have h:= Real.pi_ne_zero
    simp [h]
    have h2:= Real.pi_pos
    have ineq1: - π < 0 := by
      simp [h2]
    have ineq2: 56 * π / 180 > 0 := by
      simp [h2]
    nlinarith
    rw [show 56 * π / 180 = (56 / 180) * π by ring]
    nth_rewrite 2 [show π = 1 * π by ring]
    rw [mul_lt_mul_iff_of_pos_right]
    norm_num
    exact Real.pi_pos

  -- Then we prove the key identity --
  have cos_prod_id : ∀ n: ℕ, ∀ θ: ℝ, (sin θ ≠ 0) → ∏ k ∈ Finset.range n, cos ((2^k) * θ) = sin (2^n * θ) / (2^n * sin θ) := by
    intro n θ ne
    induction' n with n dn
    . simp
      field_simp
    . rw [Finset.prod_range_succ]
      rw [dn]
      field_simp
      have s: sin (2 ^ (n + 1) * θ) = 2 * sin (2 ^ n * θ) * cos (2 ^ n * θ) := by
        rw [show (2: ℝ)  ^ (n + 1) * θ = 2 * (2 ^ n * θ) by ring]
        rw [Real.sin_two_mul]
      rw [s]
      ring

  have h_prod : ∏ k ∈ Finset.range 24, cos ((2^k) * θ) = sin (2^24 * θ) / (2^24 * sin θ) := by
    specialize cos_prod_id 24 θ h_sin_ne
    exact cos_prod_id
  -- prove sin(2^24 * θ) = sin(θ) by using the periodicity of sin, i.e 2π ∣ (2^24 -1)θ --
  have h_sin_eq : sin (2^24 * θ) = sin (θ) := by
    simp [θ]
    rw [Real.sin_eq_sin_iff]
    use -2609789
    left
    norm_num
    field_simp
    ring_nf

  -- plug the two results into the product identity --
  rw [h_prod, h_sin_eq]
  field_simp
  ring