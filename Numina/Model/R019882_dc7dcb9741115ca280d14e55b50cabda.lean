import Mathlib

open Real
open scoped BigOperators

theorem number_theory_172963 {F : ℕ → ℝ}
  (hF : ∀ n, F (n + 2) = F n + F (n + 1))
  (hF01 : F 0 = 1 ∧ F 1 = 1) :
  ∀ m, ∑ i in Finset.Icc 0 m, (1 / (F i * F (i + 2))) < 1 := by
  have h1 : F 0 = 1 := hF01.1
  have h2 : F 1 = 1 := hF01.2
  have h3 : ∀ (n : ℕ), F (n + 2) = F n + F (n + 1) := hF
  have h5 : ∀ (n : ℕ), F n > 0 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with 
    | zero =>
      rw [h1]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [h2]
        norm_num
      | succ n =>
        have h8 := ih (n) (by linarith)
        have h9 := ih (n + 1) (by linarith)
        simp [hF] at *
        all_goals linarith
  have h4 : ∀ m : ℕ, ∑ i in Finset.Icc 0 m, (1 / (F i * F (i + 2))) = 1 - 1 / (F (m + 1) * F (m + 2)) := by 
    intro m
    induction m with
    | zero =>
      norm_num [h1, h2, hF]
      <;> field_simp [(show F 0 ≠ 0 by nlinarith [h5 0]), (show F 1 ≠ 0 by nlinarith [h5 1]), (show F 2 ≠ 0 by nlinarith [h5 2])]
      <;> norm_num
    | succ m ih =>
      have eq1 : ∑ i in Finset.Icc 0 (m + 1), (1 / (F i * F (i + 2))) = 
            ∑ i in Finset.Icc 0 m, (1 / (F i * F (i + 2))) + 1 / (F (m + 1) * F (m + 3)) := by 
        rw [Finset.sum_Icc_succ_top (by linarith)]
        <;> simp 
        <;> ring_nf
      rw [eq1]
      rw [ih]
      have eq2 : F (m + 3) = F (m + 1) + F (m + 2) := by 
        specialize h3 (m + 1)
        simpa using h3 
      field_simp [(show F (m + 1) ≠ 0 by nlinarith [h5 (m + 1)]), (show F (m + 2) ≠ 0 by nlinarith [h5 (m + 2)]), (show F (m + 3) ≠ 0 by nlinarith [h5 (m + 3)])]
      -- After field_simp, we get:
      -- However, further calculations are more explicit
      rw [eq2]
      <;> ring_nf 
      all_goals nlinarith [h5 (m + 1), h5 (m + 2), h5 (m + 3)]
  intro m 
  have h7 : ∑ i in Finset.Icc 0 m, (1 / (F i * F (i + 2))) = 1 - 1 / (F (m + 1) * F (m + 2)) := h4 m 
  rw [h7]
  -- Now bound this by 1
  have h8 : F (m + 1) > 0 := h5 (m + 1)
  have h9 : F (m + 2) > 0 := h5 (m + 2)
  have h10 : F (m + 1) * F (m + 2) > 0 := mul_pos h8 h9 
  have h11 : (1 / (F (m + 1) * F (m + 2))) > 0 := by 
    apply div_pos 
    all_goals linarith 
  linarith