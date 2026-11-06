import Mathlib

namespace Algebra_610435

-- Rounding function for integers
noncomputable def floor_int (x : ℝ) : ℤ := 
  if x  ≤ ⌊x⌋ + 0.5 then ⌊x⌋ else ⌊x⌋ + 1
  -- Floor function (rounds to nearest integer)

-- Rounding function for tenths
noncomputable def round_tenth (x : ℝ) : ℝ :=
  floor_int (10 * x) / 10  -- Round to nearest tenth


end Algebra_610435

open Algebra_610435 Rat

theorem Algebra_610435 {a b : ℝ}(ha : round_tenth a +  floor_int b = 98.6) 
  (hb : floor_int a + round_tenth b = 99.3) : floor_int (10 * (a + b)) ≥ 988 := by 
  have ineq_aux₁ : ∀ (x : ℝ), floor_int x ≥  x - 0.5 := by 
    intro x
    unfold floor_int
    split_ifs with hx
    · linarith
    have hx₁ : ⌊x⌋ + 1 > x := by simp
    calc 
      _ = ↑⌊x⌋ + 1 := by simp
      _ ≥  x := by linarith
      _ ≥  x - 0.5 := by linarith
  have ineq_aux₂ : ∀ (x : ℝ), floor_int x <  x + 0.5 := by 
    intro x
    unfold floor_int
    split_ifs with hx
    · have hx' : ⌊x⌋ ≤ x := Int.floor_le x
      linarith
    have hx' : x > ⌊x⌋ + 0.5 := by exact lt_of_not_ge hx
    calc 
      _ = (⌊x⌋: ℝ) + 0.5 + 0.5 := by 
        norm_num
        field_simp
        ring
      _ <  x + 0.5 := by 
        linarith
  have ineq_aux₃ : ∀ (x : ℝ), round_tenth x ≥  x - 0.05 := by 
    intro x
    unfold round_tenth
    have pos : (10 : ℝ) > 0 := by linarith
    apply (le_div_iff₀ pos).mpr
    ring_nf
    have aux : ↑(floor_int (x * 10)) ≥ x * 10 - 0.5 := ineq_aux₁ (x * 10)
    linarith
  have ineq_aux₄ : ∀ (x : ℝ), round_tenth x <  x + 0.05 := by 
    intro x
    unfold round_tenth
    have pos : (10 : ℝ) > 0 := by linarith
    apply (div_lt_iff₀ pos).mpr
    ring_nf
    have aux : ↑(floor_int (x * 10)) <  x * 10 + 0.5 := ineq_aux₂ (x * 10)
    linarith
  have ineq_ab : a + b > 98.75 := by 
    have aux : 99.3  < a + b + 0.55 := by
      calc 
        _ = floor_int a + round_tenth b := by 
          rw [←hb]
        _ < a + 0.5 + b + 0.05 := by 
          obtain aux₁ := ineq_aux₂ a
          obtain aux₂ := ineq_aux₄ b
          linarith
        _ = a + b + 0.55 := by 
          ring
    linarith
  have ineq_ab' : 10 * (a + b) > 987.5 := by 
    have pos : (10 : ℝ) > 0 := by linarith
    linarith
  unfold floor_int
  split_ifs with hx
  · have hx' : (⌊10 * (a + b)⌋ : ℝ) > 987 := by 
      calc 
        _ ≥ 10 * (a + b) - 0.5 := by linarith
        _ > 987.5 -0.5 := by linarith
        _ = 987 := by norm_num
    norm_cast at hx'
  have hx' : 10 * (a + b) > (⌊10 * (a + b)⌋ : ℝ) + 0.5 := by exact lt_of_not_ge hx
  have hx₁ : 10 * (a + b) ≥  987 := by linarith
  have hx₂ : ⌊10 * (a + b)⌋ ≥ 987 := by 
    exact Int.le_floor.mpr hx₁
  linarith