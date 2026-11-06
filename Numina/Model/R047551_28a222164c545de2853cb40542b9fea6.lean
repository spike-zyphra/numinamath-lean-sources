import Mathlib

open Real Finset

theorem algebra_14190
    (a S : ℕ → ℝ)
    (hS : ∀ n, S n = ∑ i ∈ Icc 0 n, a i)
    (ha0 : a 0 = 1)
    (han : ∀ n ≥ 1, a n = (2 * (S n) ^ 2) / (2 * S n - 1)) :
    a 99 = - 2 / 39203 := by

  have r1 : ∀ n ≥ 1, S n - S (n - 1) = (2 * (S n) ^ 2) / (2 * S n - 1) := by
    intro n hn
    conv => lhs; rw [hS, hS, show n = n - 1 + 1 by omega, sum_Icc_succ_top (by omega), Nat.sub_add_cancel (by omega), add_sub_cancel_left]
    exact han n hn

  have l1 : ∀ n, S n ≠ 0 := by
    intro n
    induction n with
    | zero =>
      simp [hS, ha0]
    | succ n ih =>
      by_contra! h_contra
      specialize r1 (n + 1) (Nat.le_add_left 1 n)
      simp [h_contra, ih] at r1

  have l2 : ∀ n, S n ≠ 1 / 2 := by
    intro n
    induction n with
    | zero =>
      simp [hS, ha0]
    | succ n ih =>
      by_contra! h_contra
      specialize r1 (n + 1) (by linarith)
      simp [h_contra] at r1
      rw [inv_eq_one_div] at r1
      exact ih (by linarith)

  have h1 : ∀ n, S n = 1 / (2 * n + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp [hS, ha0]
      <;> ring_nf <;> norm_num
    | succ n ih =>
      have eq1 : a (n + 1) = (2 * (S (n + 1)) ^ 2) / (2 * S (n + 1) - 1) := by
        specialize han (n + 1) (show (n + 1) ≥ 1 by omega)
        simpa using han
      have eq2 : a (n + 1) = S (n + 1) - S n := by
        have h1 : S (n + 1) = ∑ i ∈ Icc 0 (n + 1), a i := hS (n + 1)
        have h2 : S n = ∑ i ∈ Icc 0 n, a i := hS n
        rw [h1]
        rw [h2] at *
        simp [sum_Icc_succ_top, add_assoc]
        <;> linarith
      rw [eq2] at eq1
      rw [ih] at eq1
      field_simp [show S (n + 1) ≠ 0 by apply l1, show 2 * S (n + 1) - 1 ≠ 0 by
        by_contra h
        have h2 : S (n + 1) = 1 / 2 := by linarith
        specialize l2 (n + 1)
        contradiction] at eq1
      field_simp [show (2 * (n + 1 : ℝ) + 1) ≠ 0 by positivity] at eq1 ⊢
      nlinarith

  have ha99 : a 99 = (2 * (S 99) ^ 2) / (2 * S 99 - 1) := by 
    apply han 99 (by norm_num)

  have hS99 : S 99 = 1 / 199 := by 
    specialize h1 99
    norm_num at h1 ⊢
    linarith

  rw [hS99] at ha99
  norm_num [ha99]
  <;> ring_nf <;> norm_num