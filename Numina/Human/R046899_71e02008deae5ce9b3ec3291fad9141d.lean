import Mathlib

open Real

/- Find the solution set of the inequality $\tan\alpha + \frac{\sqrt{3}}{3} > 0$.-/
theorem algebra_9393 (α : ℝ) (hαne : ∀ k : ℤ, π / 2 + k * π ≠ α) : tan α + √3 / 3 > 0 ↔
    ∃ k : ℤ, α ∈ (Set.Ioo (- π / 6 + k * π) (π / 2 + k * π) : Set ℝ) := by
  -- Calculate that 1/√3=√3/3 .
  have inv_sqrt_three : 1 / √3 = √3 / 3 := by
    rw [← mul_left_inj' (show √3 ≠ 0 by norm_num)]
    conv_rhs => rw [mul_comm, ← mul_div_assoc]
    simp
  constructor
  . intro hα
    -- There exists k such that α ∈ (π/2 + kπ, 3π/2 + kπ)
    set k : ℤ := ⌊α / π - 1 / 2⌋
    have h1 : k ≤ α / π - 1 / 2 := Int.floor_le _
    have h2 : α / π - 1 / 2 < k + 1 := Int.lt_floor_add_one _
    use k + 1
    constructor
    . replace h1 : -1 / 2 ≤ α / π - (k + 1) := by linarith
      rw [← mul_le_mul_iff_of_pos_left (show 0 < π from pi_pos), mul_sub, mul_comm _ (α / π),
        div_mul_cancel₀ _ (by positivity), mul_comm _ ((k : ℝ) + 1)] at h1
      replace h2 : α / π - (k + 1) < 1 / 2 := by linarith
      replace h2 := mul_lt_mul_of_pos_left h2 (show 0 < π from pi_pos)
      rw [mul_sub, mul_comm _ (α / π), div_mul_cancel₀ _ (by positivity), mul_comm _ ((k : ℝ) + 1)] at h2
      -- We prove the result by contradiction.
      by_contra h
      push_neg at h
      push_cast at h
      replace h : α - (k + 1) * π ≤ -π / 6 := by linarith
      set θ := α - (k + 1) * π
      -- It is obivous that θ=α-(k+1)π lies in (-π/2, π/2).
      have hθmemIoo : θ ∈ Set.Ioo (-(π / 2)) (π / 2) := by
        constructor
        . rw [lt_iff_le_and_ne]
          refine ⟨by linarith, ?_⟩
          dsimp [θ]
          intro hαk
          replace hαk : π / 2 + (k : ℝ) * π = α := by linear_combination hαk
          exact hαne _ hαk
        linarith
      -- It is obvious that tanθ = tanα .
      have htanθ : tan θ = tan α := by
        dsimp [θ]
        rw [sub_eq_add_neg, ← neg_mul, show -((k : ℝ) + 1) = ((-k - 1 : ℤ) : ℝ) by norm_cast; ring, tan_add_int_mul_pi]
      rcases eq_or_ne θ (-π / 6) with hθ | hθ
      -- If θ=-π/6, there is a contradiction.
      . rw [← htanθ, hθ, neg_div, tan_neg, tan_pi_div_six, inv_sqrt_three] at hα
        norm_num at hα
      replace h : θ < -π / 6 := by
        rw [lt_iff_le_and_ne]
        constructor <;> assumption
      -- If θ<-π/6, there is also a contradiction from the monotonicity of tangent function.
      have := Real.strictMonoOn_tan (by assumption) (by constructor <;> linarith) h
      rw [neg_div, tan_neg, tan_pi_div_six, inv_sqrt_three] at this
      linarith
    have := mul_lt_mul_of_pos_left h2 (show 0 < π from pi_pos)
    rw [mul_sub, mul_comm, div_mul_cancel₀ _ (by positivity), one_div] at this
    push_cast
    rw [div_eq_mul_inv, mul_comm _ π]
    linarith
  -- Verify that if α∈(-π/6+kπ, π/2+kπ) then tanα + √3/3 > 0.
  rintro ⟨k, hk⟩
  simp at hk
  let θ := α - k * π
  have htanθ : tan θ = tan α := by
    dsimp [θ]
    rw [show α - k * π = α + (-k) * π by ring]
    exact_mod_cast tan_add_int_mul_pi _ _
  rw [← htanθ]
  -- Suffices to show tanθ > tan(-π/6)
  suffices tan θ > tan (- (π / 6)) by
    rw [tan_neg, tan_pi_div_six] at this
    linarith
  -- It is obvious from the monotonicity of tangent function.
  apply Real.strictMonoOn_tan
  . constructor <;> linarith
  . constructor <;> linarith
  . linarith
