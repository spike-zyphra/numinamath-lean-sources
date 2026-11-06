import Mathlib

def f (n : ℕ) : ℤ := match n with
| 0 => 1
| 1 => 2
| n + 2 => (f n) * (f (n + 1)) - 1

theorem algebra_271654 : f 2017 = 0 := by
  have h1 : ∀ k : ℕ, f (3 * k + 4) = 0 ∧ f (3 * k + 5) = -1 ∧ f (3 * k + 6) = -1 := by
    intro k
    induction k with
    | zero => norm_num [f]
    | succ k ih => 
      have eq1 : f (3 * (k + 1) + 4) = f (3 * k + 5) * f (3 * k + 6) - 1 := by
        simp [show 3 * (k + 1) + 4 = (3 * k + 5) + 2 by ring, f]
      have h_eq1 : f (3 * (k + 1) + 4) = 0 := by
        rw [eq1]
        have h6 : f (3 * k + 5) = -1 := ih.2.1
        have h7 : f (3 * k + 6) = -1 := ih.2.2
        simp [h6, h7]
        <;> norm_num
      have eq2 : f (3 * (k + 1) + 5) = f (3 * k + 6) * f (3 * (k + 1) + 4) - 1 := by
        simp [show 3 * (k + 1) + 5 = (3 * k + 6) + 2 by ring, f]
      have h_eq2 : f (3 * (k + 1) + 5) = -1 := by
        rw [eq2]
        have h7 : f (3 * k + 6) = -1 := ih.2.2
        have h_eq1 : f (3 * (k + 1) + 4) = 0 := by tauto
        simp [h7, h_eq1]
        <;> norm_num
      have eq3 : f (3 * (k + 1) + 6) = f (3 * (k + 1) + 4) * f (3 * (k + 1) + 5) - 1 := by
        simp [show 3 * (k + 1) + 6 = (3 * (k + 1) + 4) + 2 by ring, f]
      have h_eq3 : f (3 * (k + 1) + 6) = -1 := by
        rw [eq3]
        have h_eq1 : f (3 * (k + 1) + 4) = 0 := by tauto
        have h_eq2 : f (3 * (k + 1) + 5) = -1 := by tauto
        simp [h_eq1, h_eq2]
        <;> norm_num
      exact ⟨h_eq1, h_eq2, h_eq3⟩
  have h4000 : 2017 = 3 * 671 + 4 := by norm_num
  rw [h4000]
  exact (h1 671).1