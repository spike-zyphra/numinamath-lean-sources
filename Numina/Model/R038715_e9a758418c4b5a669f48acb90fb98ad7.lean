import Mathlib

theorem number_theory_23111 {n A B C : ℕ} (hn : n = 3 ^ 17 + 3 ^ 10) (hdiv : 11 ∣ n + 1) (hdistinct : A ≠ B ∧ A ≠ C ∧ B ≠ C)
    (hoddA : Odd A) (hoddC : Odd C) (hB : ¬ 3 ∣ B) (heq : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]):
    100 * A + 10 * B + C = 129 := by
  have h1 : n = 129199212 := by 
    norm_num [hn]
  have h2 : B = 2 := by
    rw [h1] at heq
    simp [Nat.digits, Nat.digitsAux] at heq
    omega
  have h3 : A = 1 := by 
    rw [h1] at heq
    simp [Nat.digits, Nat.digitsAux] at heq
    omega
  have h4 : C = 9 := by 
    rw [h1] at heq
    simp [Nat.digits, Nat.digitsAux] at heq
    omega
  omega