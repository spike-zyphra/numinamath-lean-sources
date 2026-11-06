import Mathlib

theorem number_theory_191695 (a b c d m : ℤ) (h₀ : 5 ∣ a * m^3 + b * m^2 + c * m + d)
    (h₁ : ¬5 ∣ d) : ∃ n, 5 ∣ d * n^3 + c * n^2 + b * n + a := by
  have h2 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  rcases h2 with (h | h | h | h | h)
  · -- $m \equiv 0 \pmod{5}$.
    have h4 : m % 5 = 0 := h
    have h5 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
      omega
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] at h5
    use 0
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ]
    <;> omega
  · -- $m \equiv 1 \pmod{5}$.
    have h4 : m % 5 = 1 := h
    have h5 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
      omega
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] at h5
    use 1
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ]
    <;> omega
  · -- $m \equiv 2 \pmod{5}$.
    have h4 : m % 5 = 2 := h
    have h5 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
      omega
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] at h5
    use 3
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ]
    <;> omega
  · -- $m \equiv 3 \pmod{5}$.
    have h4 : m % 5 = 3 := h
    have h5 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
      omega
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] at h5
    use 2
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ]
    <;> omega
  · -- $m \equiv 4 \pmod{5}$.
    have h4 : m % 5 = 4 := h
    have h5 : (a * m^3 + b * m^2 + c * m + d) % 5 = 0 := by
      omega
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4] at h5
    use 4
    simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ]
    <;> omega
  all_goals try { 
    omega
  }
  <;> try { 
    tauto 
  }
  all_goals try { 
    tauto
  }
  all_goals try { 
    omega
  }
  <;> try { 
    tauto
  }
  all_goals try { 
    tauto
  }
  all_goals try { 
    omega
  }
  <;> try { 
    tauto 
  }
  all_goals try { 
    tauto
  }
  all_goals try { 
    omega
  }
  <;> try { 
    tauto
  }
  all_goals try { 
    tauto
  }
  all_goals try { 
    tauto
  }
  <;> try { 
    omega 
  }