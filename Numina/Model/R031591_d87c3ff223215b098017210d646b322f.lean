import Mathlib

theorem number_theory_50864 {f : ℕ → ℕ} (hf : ∀ x, (Nat.divisors (f x)).card = x)
    (h : ∀ x y, f (x * y) ∣ (x - 1) * y ^ (x * y - 1) * f x) :
    f 1 = 1 ∧ ∀ p m, Nat.Prime p → f (p ^ m) = p ^ (p ^ m - 1) ∧
    (∀ x y, x ≠ 0 → y ≠ 0 → f x * f y = f (x * y)) := by

  have h1 := hf 0
  have h2 : f 0 = 0 := by
    have h3 : (Nat.divisors (f 0)).card = 0 := h1
    have h4 : Nat.divisors (f 0) = ∅ := by
      have h5 : (Nat.divisors (f 0)).card = 0 := h3
      simp at h5 ⊢
      all_goals tauto
    by_cases h11 : f 0 > 0
    · -- If f 0 > 0, then 1 divides f 0, so 1 is in divisors of f 0
      have h12 : 1 ∈ Nat.divisors (f 0) := by
        simp at *
        all_goals
        try { 
          have h13 : f 0 > 0 := h11
          omega 
        }
      rw [h4] at h12
      simp at h12
    · -- f 0 ≤ 0, so f 0 = 0
      omega

  have h3 := h 2 0
  norm_num at h3
  have h4 : f 2 = 0 := by
    rw [h2] at h3
    have h5 : (0 : ℕ) ∣ f 2 := h3
    have h6 : f 2 = 0 := by
      try omega
    exact h6

  have h7 := hf 2
  rw [h4] at h7
  simp at h7
  all_goals omega