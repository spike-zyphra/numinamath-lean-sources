import Mathlib

theorem number_theory_28368 (a : ℕ → ℤ) (ha : a 0 = 0 ∧ ∀ k, a (k + 1) = 3 * a k + 1) : 11 ∣ a 155 := by
  rcases ha with ⟨ha0, ha1⟩
  have h2 : ∀ k:ℕ, 2 * a k = 3^k -1 := by
    intro k
    induction k with
    | zero =>
      rw [ha0]
      norm_num
    | succ n ih =>
      have h3 : a (n + 1) = 3 * a n + 1 := ha1 n
      have eq1 : 2 * a (n + 1) = 2 * (3 * a n + 1) := by
        rw [h3]
      have eq2 : 2 * (3 * a n + 1) = 6 * a n + 2 := by
        ring
      rw [eq1, eq2]
      have h3' : 2 * a n = (3^n - 1 : ℤ) := by
        simpa using ih
      have eq4 : 6 * a n = 3 * (2 * a n) := by ring
      have eq5 : 6 * a n + 2 = (3^(n + 1) -1 : ℤ) := by 
        have h3' : 2 * a n = (3^n - 1 : ℤ) := by
          simpa using ih
        have eq6 : 3 * (2 * a n) = (3 * (3^n - 1 : ℤ)) := by
          rw [h3']
        have eq7 : 3 * (3^n -1 : ℤ) = (3^(n + 1) -3 : ℤ) := by
          ring_nf
        omega
      omega
  have h3 : 2 * a 155 = 3^155 -1 := h2 155
  have h4 : a 155 = (3^155 -1) / 2 := by
    omega
  rw [h4]
  have h5 : (3^155 -1 : ℤ) % 11 = 0 := by
    norm_num [Int.ModEq, pow_add, pow_mul]
  have h6 : ((3^155 -1) / 2 : ℤ) % 11 = 0 := by 
    omega
  omega