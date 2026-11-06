import Mathlib

theorem number_theory_281929 {a b : ℤ} (hab : a ≠ b) (h : a % (a - b) = b % (a - b)) :
    ∀ m : ℕ, a ^ m % (a - b) = b ^ m % (a - b) ∧ (a ^ m - b ^ m) % (a - b) = 0 := by 
  intro m 
  have h1 : ∀ m : ℕ, a ^ m % (a - b) = b ^ m % (a - b) := by 
    intro m 
    induction m with 
    | zero => 
      simp 
    | succ m ih => 
      have h2 : a ^ (m + 1) % (a - b) = b ^ (m + 1) % (a - b) := by 
        have h3 : a ^ (m + 1) = a * (a ^ m) := by ring 
        have h4 : b ^ (m + 1) = b * (b ^ m) := by ring 
        rw [h3, h4] 
        simp [Int.mul_emod, ih, h] 
      exact h2 
  constructor 
  · -- Show that a ^ m % (a - b) = b ^ m % (a - b)
    apply h1 m 
  · -- Show that (a ^ m - b ^ m) % (a - b) = 0 
    have h3 : a ^ m % (a - b) = b ^ m % (a - b) := h1 m 
    simp [Int.sub_emod, h3]