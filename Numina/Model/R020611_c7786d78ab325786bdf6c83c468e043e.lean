import Mathlib

theorem algebra_67090 {a b : ℂ} (P : ℂ → ℂ) (hP : P = fun t => a ^ t + b ^ t)
    (hP1 : P 1 = 7) (hP2 : P 3 = 28) : P 2 = 19 := by
  have eq1 : a + b = 7 := by
    rw [hP] at hP1
    simp [pow_one] at hP1 
    exact hP1

  have eq2 : a^3 + b^3 = 28 := by 
    rw [hP] at hP2 
    simp at hP2 
    exact hP2

  have eq3 : a^3 + b^3 = (a + b)^3 - 3 * (a * b) * (a + b) := by 
    ring_nf

  rw [eq1] at eq3 
  have eq4 : a^3 + b^3 = 7^3 - 3 * (a * b) * 7 := by 
    simpa using eq3

  rw [eq4] at eq2

  have eq5 : a * b = 15 := by
    norm_num [pow_three] at eq2 ⊢ 
    simp [Complex.ext_iff] at eq2 ⊢
    constructor <;> 
      nlinarith

  have h1 : P 2 = a^2 + b^2 := by 
    rw [hP]
    simp

  have eq6 : a^2 + b^2 = 19 := by
    have : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by 
      ring_nf
    rw [this, eq1, eq5]
    norm_num

  rw [h1]
  exact_mod_cast eq6