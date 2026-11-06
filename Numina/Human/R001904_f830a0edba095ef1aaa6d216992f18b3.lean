import Mathlib

theorem number_theory_43828 :
    ∑ᶠ r ∈ {r : ℝ | 0 < r ∧ 25 * Int.fract r + ⌊r⌋ = 125}, r = 2837 := by
  suffices H : {r : ℝ | 0 < r ∧ 25 * Int.fract r + ⌊r⌋ = 125} = (Finset.range 25).map { toFun := fun (k : ℕ) ↦ (125 - 24 / 25 * k : ℝ), inj' := by intro k₁ k₂; simp } by
    rw [H, finsum_mem_coe_finset]
    norm_num
  ext r
  constructor
  simp
  . intro hr h
    replace h : 25 * Int.fract r = 125 - ⌊r⌋ := by linarith only [h]
    have ⟨k, hk⟩ : ∃ (k : ℕ), k = 125 - ⌊r⌋ := by
      refine CanLift.prf _ ?_
      rify
      calc
        0 ≤ 25 * Int.fract r := by simp
        _ = 125 - ⌊r⌋ := h
    use k
    rify at hk ⊢
    constructor
    . rw [hk, ← h]
      simp [Int.fract_lt_one]
    . calc (125 - 24 / 25 * k : ℝ)
        _ = 125 - k + k / 25 := by ring
        _ = ⌊r⌋ + Int.fract r := by linarith
        _ = r :=  Int.floor_add_fract r
  . simp
    intro k hk h
    constructor
    . rify at hk
      linarith
    . have H : Int.fract r = k / 25 := by
        rw [Int.fract_eq_iff]
        refine ⟨?_, ?_, ?_⟩
        . positivity
        . rify at hk
          linarith only [hk]
        . use 125 - k
          simp
          linarith only [h]
      rw [← Int.self_sub_fract]
      linarith
