import Mathlib

theorem algebra_138570 {p q r : ℝ} (hpqr : p > 0 ∧ q > 0 ∧ r > 0) (hq : q > 0)
    (hqr : p > r) (a b : ℕ → ℝ) (ha1 : a 1 = p) (hb1 : b 1 = q)
    (han : ∀ n ≥ 2, a n = p * a (n - 1)) (hbn : ∀ n ≥ 2, b n = q * a (n - 1) + r * b (n - 1)) :
    ∀ n ≥ 2, b n = q * (p ^ n - r ^ n) / (p - r) := by

  have ha : ∀ n, a (n + 1) = p ^ (n + 1) := by 
    intro n 
    induction n with 
    | zero => 
      simp [ha1]
    | succ n ih => 
      calc 
        a ((n + 1) + 1) 
          = p * a (n + 1) := by 
            specialize han (n + 2) (by linarith)
            simpa using han 
        _ = p * (p ^ (n + 1)) := by 
          rw [ih] 
        _ = p ^ (n + 2) := by 
          ring 

  intro n hn 
  have eq1 : ∀ (n : ℕ), b (n + 2) = q * (p ^ (n + 2) - r ^ (n + 2)) / (p - r) := by 
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero => 
      calc 
        b 2 = q * a 1 + r * b 1 := by 
          specialize hbn 2 (by linarith)
          simpa using hbn
        _ = q * p + r * q := by 
          rw [ha1, hb1]
        _ = q * (p + r) := by ring 
        _ = q * (p ^ 2 - r ^ 2) / (p - r) := by 
          field_simp [(show p - r ≠ 0 by linarith)]
          <;> ring
    | succ n =>
      have eq3 : b (n + 3) = q * a (n + 2) + r * b (n + 2) := by 
        specialize hbn (n + 3) (by linarith)
        simpa using hbn 
      have eq4 : a (n + 2) = p ^ (n + 2) := by 
        specialize ha (n + 1)
        simpa using ha
      have eq5 : b (n + 2) = q * (p ^ (n + 2) - r ^ (n + 2)) / (p - r) := by 
        apply ih (n) (by linarith)
      rw [eq4] at eq3
      rw [eq5] at eq3
      rw [eq3]
      field_simp [(show p - r ≠ 0 by linarith)]
      ring_nf

  have eq2 : b n = q * (p ^ n - r ^ n) / (p - r) := by 
    have eq1' : b (n - 2 + 2) = q * (p ^ (n - 2 + 2) - r ^ (n - 2 + 2)) / (p - r) := by 
      apply eq1 (n - 2)
    have eq6 : (n - 2 + 2 : ℕ) = n := by omega 
    rw [eq6] at eq1' 
    rw [eq1']
    <;> simp [pow_add, pow_mul] 
    <;> ring_nf 
  exact eq2