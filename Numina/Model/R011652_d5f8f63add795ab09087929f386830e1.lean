import Mathlib

open Polynomial

theorem algebra_273867 : ¬∃ a b c d : ℤ, (X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d) =
    X ^ 4 + 2 * X ^ 2 + 2 * X + 2 := by 
  rintro ⟨a, b, c, d, heq⟩
  have eq1 := congr_arg (λ f => f.eval 0) heq
  simp [pow_two, pow_succ, eval_mul, eval_add, eval_C, eval_X] at eq1
  have eq2 := congr_arg (λ f => f.eval 1) heq
  simp [pow_two, pow_succ, eval_mul, eval_add, eval_C, eval_X] at eq2
  have eq3 := congr_arg (λ f => f.eval 2) heq
  simp [pow_two, pow_succ, eval_mul, eval_add, eval_C, eval_X] at eq3
  have eq4 := congr_arg (λ f => f.eval 3) heq
  simp [pow_two, pow_succ, eval_mul, eval_add, eval_C, eval_X] at eq4
  have h1 : b * d = 2 := by nlinarith
  have h2 : b ∣ 2 := by
    use d
    all_goals nlinarith
  have h3 : d ∣ 2 := by
    use b
    all_goals nlinarith
  have h4 : b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2 := by
    have h5 : b ∣ 2 := h2
    have h6 : b ≤ 2 := by
      exact Int.le_of_dvd (by norm_num) h5
    have h7 : b ≥ -2 := by
      have h8 : (-b) ∣ 2 := by
        exact Int.neg_dvd.2 h5
      have h9 : -b ≤ 2 := by
        exact Int.le_of_dvd (by norm_num) h8
      omega
    interval_cases b <;> try { tauto }
  rcases h4 with (hb | hb | hb | hb)
  · -- Case b = 1, so d = 2
    have hd : d = 2 := by 
      rw [hb] at h1
      linarith
    have ha : a = 2 := by 
      rw [hd, hb] at eq2
      nlinarith
    nlinarith
  · -- Case b = -1, so d = -2
    have hd : d = -2 := by 
      rw [hb] at h1
      linarith
    have ha : a = -2 := by 
      rw [hd, hb] at eq2
      nlinarith
    nlinarith
  · -- Case b = 2, so d = 1
    have hd : d = 1 := by 
      rw [hb] at h1
      linarith
    have ha : a = -2 := by 
      rw [hd, hb] at eq2
      nlinarith
    nlinarith
  · -- Case b = -2, so d = -1
    have hd : d = -1 := by 
      rw [hb] at h1
      linarith
    have ha : a = 2 := by 
      rw [hd, hb] at eq2
      nlinarith
    nlinarith