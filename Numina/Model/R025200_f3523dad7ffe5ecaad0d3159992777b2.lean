import Mathlib

theorem number_theory_5802 (N : ℕ) (hN : ∃! n : ℕ, 0 < n ∧ IsSquare (n * 880 / 100) ∧
    n * 880 / 100 < 880 ∧ n = N) : (Nat.digits 10 N).sum = 10 := by
  rcases hN with ⟨n, ⟨hn_pos, hn_sq, hn_lt, hn_eq⟩, h⟩
  have h_eq : n = 55 := by 
    have h5 : n ≤ 99 := by
      omega
    have h8 : ∃ r, n * 880 / 100 = r * r := by
      obtain ⟨r, hr⟩ := hn_sq
      refine ⟨r, by linarith⟩
    rcases h8 with ⟨r, hr_eq⟩
    have h9 : r ≤ 29 := by
      nlinarith
    interval_cases n <;> norm_num at hn_sq hn_lt hr_eq <;> try { 
      { 
        interval_cases r <;> omega 
      }
    }
    <;> try { omega }
  have hN_eq : N = 55 := by
    omega
  calc
    (Nat.digits 10 N).sum = (Nat.digits 10 55).sum := by rw [hN_eq]
    _ = (Nat.digits 10 55).sum := by rfl
    _ = [5, 5,].sum := by native_decide
    _ = 5 + 5 := by simp
    _ = 10 := by norm_num