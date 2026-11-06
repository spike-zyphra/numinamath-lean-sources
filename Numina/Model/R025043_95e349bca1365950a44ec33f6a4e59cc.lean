import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_142393 (a : ℕ → ℝ) (ha : ∀ n, a n = (1 + 3 * n) / (6 - n)) (ε : ℝ)
  (hε : ε > 0) : ∃ N, ∀ n, N ≤ n → |a n + 3| < ε := by 

  use max 7 (Nat.ceil (6 + 19 / ε) + 1)
  intro n hn
  have h1 : n ≥ max 7 (Nat.ceil (6 + 19 / ε) + 1) := by
    linarith

  have h2 : n ≥ 7 := by 
    cases max_cases 7 (Nat.ceil (6 + 19 / ε) + 1) with
    | inl h3 => linarith
    | inr h3 => linarith

  have h3 : n ≥ Nat.ceil (6 + 19 / ε) + 1 := by
    cases max_cases 7 (Nat.ceil (6 + 19 / ε) + 1) with
    | inl h4 => linarith
    | inr h4 => linarith

  have h4 : a n = (1 + 3 * (n : ℝ)) / (6 - (n : ℝ)) := by
    specialize ha n
    simpa using ha

  have h5 : a n + 3 = (19 : ℝ) / (6 - (n : ℝ)) := by
    rw [h4]
    field_simp [(show (6 - (n : ℝ)) ≠ 0 by
      have h6 : (n : ℝ) ≥ (7 : ℝ) := by
        have h7' : n ≥ 7 := h2
        exact_mod_cast h7'
      nlinarith
    )]
    <;> ring

  have h20 : (n : ℝ) ≥ (7 : ℝ) := by
    have h7' : n ≥ 7 := h2
    exact_mod_cast h7'

  have h6 : (6 - (n : ℝ) : ℝ) < (0 : ℝ) := by
    nlinarith

  have h7 : |(6 - (n : ℝ) : ℝ)| = (n : ℝ) - 6 := by
    rw [abs_of_neg h6]
    all_goals
    nlinarith

  have h8 : |((19 : ℝ) / (6 - (n : ℝ)) )| = (19 / ((n : ℝ) - 6) ) := by
    have h10 : |(6 - (n : ℝ) : ℝ)| = (n - 6 : ℝ) := h7
    have h11 : |((19 : ℝ) / (6 - (n : ℝ)) )| = |(19 : ℝ)| / |(6 - (n : ℝ) )| := by 
      field_simp [abs_div]
    have h12 : |(19 : ℝ)| = (19 : ℝ) := by 
      norm_num
    rw [h12] at h11
    rw [show |(6 - (n : ℝ) )| = (n - 6 : ℝ) by linarith [h10]] at h11
    all_goals
    field_simp [(show (n - (6 : ℝ)) ≠ 0 by
      have h6' : (n : ℝ) ≥ (7 : ℝ) := h20
      nlinarith
    )] at h11 ⊢
    <;> linarith

  rw [show |a n + 3| = |(a n + 3 : ℝ)| by simp]
  rw [show a n + 3 = (19 : ℝ) / (6 - (n : ℝ)) by linarith [h5]]
  rw [h8] at *
  have h8 : (n : ℝ) ≥ (Nat.ceil (6 + 19 / ε) + 1 : ℝ) := by
    have h9 : n ≥ Nat.ceil (6 + 19 / ε) + 1 := h3
    exact_mod_cast h9

  have h11 : (n : ℝ) > (6 + 19 / ε : ℝ) := by
    have h12 : (n : ℝ) ≥ (Nat.ceil (6 + 19 / ε) + 1 : ℝ) := h8
    have h13 : (Nat.ceil (6 + 19 / ε) : ℝ) ≥ (6 + 19 / ε : ℝ) := by
      have h14 : (Nat.ceil (6 + 19 / ε) : ℝ) ≥ (6 + 19 / ε : ℝ) := by
        have h15 : (↑(Nat.ceil (6 + 19 / ε)) : ℝ) ≥ (6 + 19 / ε : ℝ) := by
          simpa using Nat.le_ceil (6 + 19 / ε : ℝ)
        exact_mod_cast h15 
      linarith
    have h15 : (Nat.ceil (6 + 19 / ε) + 1 : ℝ) > (6 + 19 / ε : ℝ) := by
      have h14 : (Nat.ceil (6 + 19 / ε) : ℝ) ≥ (6 + 19 / ε : ℝ) := h13 
      have h17 : (Nat.ceil (6 + 19 / ε) + 1 : ℝ) > (6 + 19 / ε) := by 
        have h14a : (Nat.ceil (6 + 19 / ε) : ℝ) ≥ (6 + 19 / ε : ℝ) := h13 
        nlinarith
      linarith
    nlinarith
  have h9' : (n - 6 : ℝ) > (19 / ε : ℝ) := by
    nlinarith

  have h14 : (19 / ((n - 6 : ℝ)) ) < (ε : ℝ) := by
    have h7' : (n - 6 : ℝ) > 0 := by
      nlinarith
    have h8' : (n - 6 : ℝ) > (19 / ε : ℝ) := h9'
    have h17 : (ε : ℝ) > 0 := hε
    have h19 : (ε * ((n - 6 : ℝ)) > (19 : ℝ) ) := by
      have h20 : (n - 6 : ℝ) > 0 := h7'
      have h21 : (ε : ℝ) > 0 := hε
      have h22 : (n - 6 : ℝ) > (19 / ε : ℝ) := h8'
      have h23 : (ε : ℝ) * ((n - 6 : ℝ)) > (ε : ℝ) * (19 / ε : ℝ) := by
        apply mul_lt_mul_of_pos_left h22 hε
      have h24 : (ε : ℝ) * (19 / ε : ℝ) = (19 : ℝ) := by
        field_simp [show (ε : ℝ) ≠ 0 by linarith]
      linarith
    have h18 : (19 / ((n - 6 : ℝ)) ) < (ε : ℝ) := by
      have h15 : (n - 6 : ℝ) > 0 := h7'
      have h21 : (ε * ((n - 6) : ℝ)) > (19 : ℝ) := h19 
      have h22 : (ε : ℝ) = (ε * ((n - 6) : ℝ) ) / ((n - 6) : ℝ) := by 
        field_simp [show (n - 6 : ℝ) ≠ 0 by linarith]
      have h23 : (19 / ((n - 6) : ℝ) ) = (19 ) / ((n - 6) : ℝ) := by rfl
      have h24 : (19 / ((n - 6) : ℝ) ) < ((ε * ((n - 6) : ℝ) ) / ((n - 6) : ℝ) ) := by
        apply (div_lt_div_right (by linarith )).mpr
        nlinarith
      have h25 : (ε * ((n - 6) : ℝ) ) / ((n - 6) : ℝ) = (ε : ℝ) := by 
        field_simp [show (n - 6 : ℝ) ≠ 0 by linarith]
      linarith
    linarith
  linarith