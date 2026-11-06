import Mathlib
open Real

/-
Andrea flips a fair coin repeatedly, continuing until she either flips two heads in a row (the sequence $H H$ ) or flips tails followed by heads (the sequence $T H$ ). What is the probability that she will stop after flipping $H H$ ?

Let P_start be the probability that Andrea stops with HH, starting from the beginning.
Let P_H be the probability that Andrea stops with HH, given the previous flip was H.
Let P_T be the probability that Andrea stops with HH, given the previous flip was T.

The system of equations is:
1. P_start = (1/2) * P_H + (1/2) * P_T
2. P_H     = (1/2) * 1 + (1/2) * P_T
3. P_T     = (1/2) * 0 + (1/2) * P_T
-/

-- Theorem to solve for P_T
lemma solve_P_T (P_T : ℝ) (h_eq3 : P_T = (1/2 : ℝ) * 0 + (1/2 : ℝ) * P_T) : P_T = 0 := by linarith

-- Theorem to solve for P_H
lemma solve_P_H (P_H P_T : ℝ) (h_eq2 : P_H  = (1/2 : ℝ) * 1 + (1/2 : ℝ) * P_T) (h_P_T_is_0 : P_T = 0) : P_H = (1/2 : ℝ) := by
  -- From h_eq2: P_H = (1/2)*1 + (1/2)*P_T
  -- Substitute P_T = 0
  rw [h_eq2, h_P_T_is_0]
  simp -- Simplifies (1/2)*0 to 0 and x + 0 to x

-- Theorem to solve for P_start
lemma solve_P_start (P_start P_H P_T : ℝ) (h_eq1 : P_start = (1/2 : ℝ) * P_H + (1/2 : ℝ) * P_T) (h_P_H_is_half : P_H = (1/2 : ℝ)) (h_P_T_is_0 : P_T = 0) : P_start = (1/4 : ℝ) := by
  -- From h_eq1: P_start = (1/2)*P_H + (1/2)*P_T
  -- Substitute P_H = 1/2 and P_T = 0
  rw [h_eq1, h_P_H_is_half, h_P_T_is_0]
  simp -- Simplifies (1/2)*0 to 0 and x + 0 to x
  norm_num -- Simplifies (1/2)*(1/2) to 1/4

theorem combinatorics_611214 :
    (∀ (P_s P_h P_t : ℝ),
      P_s = (1/2 : ℝ) * P_h + (1/2 : ℝ) * P_t →
      P_h = (1/2 : ℝ) * 1 + (1/2 : ℝ) * P_t →
      P_t = (1/2 : ℝ) * 0 + (1/2 : ℝ) * P_t →
      P_s = (1/4 : ℝ)) := by
  intros P_s P_h P_t eq1 eq2 eq3
  have val_P_T : P_t = 0 := solve_P_T P_t eq3
  have val_P_H : P_h = (1/2 : ℝ) := solve_P_H P_h P_t eq2 val_P_T
  exact solve_P_start P_s P_h P_t eq1 val_P_H val_P_T


