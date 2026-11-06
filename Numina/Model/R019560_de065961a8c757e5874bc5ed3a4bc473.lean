import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327354 (f : ℝ → ℝ) (hf : f = λ x => 27^x - 3^(x + 3) + 1) :
    IsLeast {y | ∃ x ∈ Icc 0 3, f x = y} (-53) := by
  constructor
  · -- Show -53 is attained
    use 1
    constructor
    · -- Show 1 ∈ [0, 3]
      norm_num [mem_Icc]
    · -- Show f(1) = -53
      rw [hf]
      norm_num
      all_goals norm_num
  · -- Show -53 is indeed the minimum
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 3 := hx.2
    have h1 : (27 : ℝ) ^ (x : ℝ) - (3 : ℝ) ^ (x + 3 : ℝ) + 1 ≥ -53 := by
      have h2 : (3 : ℝ) ^ (x : ℝ) ≥ (1 : ℝ) := by
        have h30 : (3 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          norm_num
        have h3x : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (x : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
          all_goals nlinarith
        linarith
      have h3 : (3 : ℝ) ^ (x : ℝ) ≤ (27 : ℝ) := by
        have h4 : (3 : ℝ) ^ (x : ℝ) ≤ (3 : ℝ) ^ (3 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
          all_goals nlinarith
        have h50 : (3 : ℝ) ^ (3 : ℝ) = (27 : ℝ) := by
          norm_num
        linarith
        all_goals nlinarith
      have h4 : (27 : ℝ) ^ (x : ℝ) = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by
        calc
          (27 : ℝ) ^ (x : ℝ) = (3 ^ (3 : ℝ) : ℝ) ^ (x : ℝ) := by norm_num
          _ = (3 : ℝ) ^ (3 * x : ℝ) := by
            rw [← Real.rpow_mul]
            ring_nf
            all_goals nlinarith
          _ = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by
            calc
              (3 : ℝ) ^ (3 * x : ℝ) = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by
                calc
                  (3 : ℝ) ^ (3 * x : ℝ) = (3 : ℝ) ^ (3 * x : ℝ) := by rfl
                  _ = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul]
                    ring_nf
                    all_goals nlinarith
              _ = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by rfl
              _ = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by rfl
              _ = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by rfl
          _ = ((3 : ℝ) ^ (x : ℝ)) ^ 3 := by rfl
      have h6 : (3 : ℝ) ^ (x + 3 : ℝ) = (3 : ℝ) ^ (x : ℝ) * (27 : ℝ) := by
        have h7 : (3 : ℝ) ^ (x + 3 : ℝ) = (3 : ℝ) ^ (x : ℝ) * (3 : ℝ) ^ (3 : ℝ) := by
          rw [← Real.rpow_add]
          ring_nf
          all_goals nlinarith
        have h50 : (3 : ℝ) ^ (3 : ℝ) = (27 : ℝ) := by
          norm_num
        rw [h7, h50]
      rw [h4, h6]
      nlinarith [sq_nonneg ((3 : ℝ) ^ (x : ℝ) - 3), sq_nonneg ((3 : ℝ) ^ (x : ℝ) ^ 2 - 9), sq_nonneg ((3 : ℝ) ^ (x : ℝ) - 3), sq_nonneg ((3 : ℝ) ^ (x : ℝ) - 3)]
      all_goals nlinarith
      <;> norm_num
      all_goals nlinarith
      <;> norm_num
      <;> nlinarith
    have h2 : ((fun (x : ℝ) => (27 : ℝ) ^ x - (3 : ℝ) ^ (x + 3) + 1) x) = (27 : ℝ) ^ (x : ℝ) - (3 : ℝ) ^ (x + 3) + 1 := by
      simp
    linarith
    all_goals tauto
    all_goals try linarith
    <;> nlinarith