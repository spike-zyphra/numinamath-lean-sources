import Mathlib

open Real
open scoped BigOperators

theorem number_theory_61536 {F : ℕ → ℝ}
  (hF : ∀ n, F (n + 2) = F n + F (n + 1))
  (hF01 : F 0 = 1 ∧ F 1 = 1)
  (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / (F n * F (n + 2))) :
  ∀ m, ∑ i in Finset.Icc 0 m, a i < 1 := by
  intro m
  have h1 : F 0 = 1 := hF01.1
  have h2 : F 1 = 1 := hF01.2
  have h3 : ∀ (n : ℕ), F (n + 2) = F n + F (n + 1) := hF
  -- proof for all the terms in the form of F n > 0
  have h3' : ∀ n, F n > 0 := by 
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      rw [h1]
      all_goals norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [h2]
        all_goals norm_num
      | succ n =>
        have h3_1 : F (n + 2) = F n + F (n + 1) := h3 n
        have h4 : F n > 0 := ih n (by linarith)
        have h5 : F (n + 1) > 0 := ih (n + 1) (by linarith)
        have h6 : F (n + 2) > 0 := by 
          linarith [h4, h5]
        simp [h3_1] at *
        all_goals nlinarith
  have h5 : ∀ (m : ℕ), ∑ i in Finset.Icc 0 m, a i = 1 - 1 / (F (m + 1) * F (m + 2)) := by
    intro m 
    induction m with 
    | zero =>
      norm_num [Finset.sum_singleton, ha, h1, h2, h3]
      <;> norm_num [h1, h2, h3]
      <;> linarith
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      rw [ha (m + 1)]
      have eq1 : F (m + 3) = F (m + 1) + F (m + 2) := by 
        specialize h3 (m + 1)
        simpa using h3
      have eq2 : 1 - 1 / (F (m + 1) * F (m + 2)) + 1 / (F (m + 1) * F (m + 3)) = 
          1 - 1 / (F (m + 2) * F (m + 3)) := by 
        have eq3 : F (m + 3) = F (m + 1) + F (m + 2) := eq1 
        rw [eq3] 
        have eq3 : F (m + 1) > 0 := h3' (m + 1)
        have eq4 : F (m + 2) > 0 := h3' (m + 2)
        have eq5 : F (m + 3) > 0 := by 
          nlinarith [eq1, h3' (m + 1), h3' (m + 2)]
        field_simp 
        <;> ring_nf <;> simp [h3] 
        <;> nlinarith [sq_nonneg (F (m + 1)), sq_nonneg (F (m + 2)), sq_nonneg (F (m + 3)), h1, h2]
      rw [eq2]
      all_goals norm_num 
      <;> ring_nf <;> norm_num
  have h5' := h5 m 
  have pos1 : F (m + 1) > 0 := h3' (m + 1)
  have pos2 : F (m + 2) > 0 := h3' (m + 2)
  have pos3 : F (m + 1) * F (m + 2) > 0 := by positivity 
  rw [h5']
  have h5 : 1 - 1 / (F (m + 1) * F (m + 2)) < 1 := by
    have pos1 : 1 / (F (m + 1) * F (m + 2)) > 0 := by positivity 
    linarith 
  linarith