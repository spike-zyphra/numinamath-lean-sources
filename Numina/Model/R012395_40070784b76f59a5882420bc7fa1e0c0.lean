import Mathlib

theorem number_theory_611020 (P : ℕ → ℤ) (hP : P 0 = 1 ∧ P 1 = 3)
    (hP' : ∀ n, P (n + 2) = P (n + 1) * P n - P n) :
    3 ∣ P 2001 := by 
  have h1 : P 0 = 1 := hP.1
  have h2 : P 1 = 3 := hP.2
  have h3 : ∀ k : ℕ, P (2 * k + 1) % 3 = 0 := by
    intro k 
    induction k with 
    | zero =>
      simp [h2]
      <;> omega
    | succ k ih =>
      have h4 : P (2 * (k + 1) + 1) % 3 = 0 := by 
        have h5 : P (2 * (k + 1) + 1) = P (2 * k + 3) := by 
          ring_nf
        rw [h5]
        have h6 : P (2 * k + 3) = P (2 * k + 2) * P (2 * k + 1) - P (2 * k + 1) := by
          specialize hP' (2 * k + 1)
          simpa using hP'
        rw [h6]
        have h7 : P (2 * k + 1) % 3 = 0 := by 
          omega 
        have h8 : (P (2 * k + 2) * P (2 * k + 1) - P (2 * k + 1)) % 3 = 0 := by 
          simp [Int.mul_emod, Int.sub_emod, h7] 
          <;> omega 
        omega 
      exact h4 
  have h4 : P 2001 % 3 = 0 := by 
    specialize h3 1000 
    norm_num at h3 ⊢ 
    all_goals omega 
  omega