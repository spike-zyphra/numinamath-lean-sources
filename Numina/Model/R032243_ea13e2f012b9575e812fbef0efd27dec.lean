import Mathlib

theorem algebra_19125 {n : ℕ} (hn : n > 0) (h : Even n) (h' : (n + 2)^2 - n^2 = 60) :
    n + (n + 2) = 30 := by
  have eq1 : (n + 2 : ℕ) ^ 2 = n ^ 2 + 4 * n + 4 := by
    ring_nf
  have eq2 : (n + 2 : ℕ) ^ 2 - n ^ 2 = 4 * n + 4 := by 
    rw [eq1]
    cases n with
    | zero => 
      omega -- contradicts with hn
    | succ n => 
      simp [Nat.add_sub_cancel_left, Nat.add_assoc]
      all_goals ring_nf <;> omega
  rw [eq2] at h'
  have hn1 : n = 14 := by
    omega
  calc
    n + (n + 2) = 14 + (14 + 2) := by rw [hn1]
    _ = 14 + 16 := by rfl
    _ = 30 := by norm_num