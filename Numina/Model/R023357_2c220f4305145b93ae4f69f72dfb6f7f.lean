import Mathlib

open Real Polynomial

theorem inequalities_35941 {a b c d : ℝ}
    (P : ℝ → ℝ)
    (hP : ∀ x, P x = a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP' : ∀ x, |x| ≤ 1 → |P x| ≤ 1) :
    |a| + |b| + |c| + |d| ≤ 7 := by

  have h1 := hP' 1 (by norm_num)
  rw [hP] at h1
  have h2 : -1 ≤ a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d := by linarith [abs_le.mp h1]
  have h3 : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d ≤ 1 := by linarith [abs_le.mp h1]

  have h1' := hP' (-1) (by norm_num)
  rw [hP] at h1'
  have h4 : -1 ≤ a * (-1) ^ 3 + b * (-1) ^ 2 + c * (-1) + d := by linarith [abs_le.mp h1']
  have h5 : a * (-1) ^ 3 + b * (-1) ^ 2 + c * (-1) + d ≤ 1 := by linarith [abs_le.mp h1']

  have h6 := hP' 0 (by norm_num)
  rw [hP] at h6
  have h7 : -1 ≤ a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d := by linarith [abs_le.mp h6]
  have h8 : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d ≤ 1 := by linarith [abs_le.mp h6]

  have h9 := hP' (1 / 2) (by
          norm_num [abs_le]
  )
  rw [hP] at h9
  have h10 : -1 ≤ a * (1 / 2) ^ 3 + b * (1 / 2) ^ 2 + c * (1 / 2) + d := by linarith [abs_le.mp h9]
  have h11 : a * (1 / 2) ^ 3 + b * (1 / 2) ^ 2 + c * (1 / 2) + d ≤ 1 := by linarith [abs_le.mp h9]

  have h12 := hP' (-1 / 2) (by
          norm_num [abs_le]
  )
  rw [hP] at h12
  have h13 : -1 ≤ a * (-1 / 2) ^ 3 + b * (-1 / 2) ^ 2 + c * (-1 / 2) + d := by linarith [abs_le.mp h12]
  have h14 : a * (-1 / 2) ^ 3 + b * (-1 / 2) ^ 2 + c * (-1 / 2) + d ≤ 1 := by linarith [abs_le.mp h12]

  cases' abs_cases a with ha ha <;> 
  cases' abs_cases b with hb hb <;> 
  cases' abs_cases c with hc hc <;> 
  cases' abs_cases d with hd hd <;> 
  all_goals 
    linarith