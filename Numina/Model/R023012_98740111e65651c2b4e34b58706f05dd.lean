import Mathlib

theorem number_theory_192774 (x y : ℤ) : 9 * x + 2 = (y + 1) * y ↔ ∃ k : ℤ, x = k * (k + 1) ∧ y = 3 * k + 1 := by
  constructor
  · -- Assume 9x + 2 = y(y+1), prove exists k, x = k(k+1) and y = 3k+1
    intro h0
    have h1 : (2 * y + 1) ^ 2 = 36 * x + 9 := by
      nlinarith [h0]
    have h2 : y % 3 = 1 := by
      have eq1 : (2 * y + 1) ^ 2 % 3 = 0 := by
        have h3 : (2 * y + 1) ^ 2 = 36 * x + 9 := h1
        have h4 : (2 * y + 1) ^ 2 % 3 = (36 * x + 9) % 3 := by
          rw [h3]
        rw [h4] at *
        omega
      have eq2 : (2 * y + 1) % 3 = 0 ∨ (2 * y + 1) % 3 = 1 ∨ (2 * y + 1) % 3 = 2 := by
        omega
      rcases eq2 with (h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h] at eq1 <;> try { omega }
    -- Now we can write y = 3k + 1
    have h3 : ∃ k : ℤ, y = 3 * k + 1 := by
      refine' ⟨(y - 1) / 3, by omega⟩
    rcases h3 with ⟨k, hk⟩
    have hx : x = k * (k + 1) := by
      rw [show y = 3 * k + 1 by linarith] at h0
      nlinarith
    exact ⟨k, by nlinarith, by nlinarith⟩
  · -- Assume exists k, x = k(k+1) and y = 3k+1, prove 9x + 2 = (y+1)y
    rintro ⟨k, hk1, hk2⟩
    rw [show x = k * (k + 1) by linarith] 
    rw [show y = 3 * k + 1 by linarith] 
    all_goals 
      nlinarith