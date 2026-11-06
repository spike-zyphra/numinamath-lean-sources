import Mathlib

/-
15th Mexico 2001 Problem A1 Find all 7-digit numbers which are multiples of 21 and which have each digit 3 or 7.
-/

theorem number_theory_122341 (n:ℕ) (hn: (Nat.digits 10 n) = [a0,a1,a2,a3,a4,a5,a6]):
((21 ∣ n) ∧ (∀a:ℕ, (a ∈ Nat.digits 10 n) → (a = 3 ∨ a = 7)))
↔
n = 3373377 ∨ n = 7373373 ∨ n = 7733733 ∨ n = 3733737 ∨ n = 7337337 ∨ n = 3777333 := by

  constructor

  --From left to right, we enumerate the cases.
  intro h
  obtain ⟨d21h, h⟩ := h

  --We express n by the digits.
  have eq : n = a6 * 10^6 + a5 * 10^5 + a4*10^4 + a3*10^3 + a2*10^2 + a1*10 + a0 := by
    have : n = Nat.ofDigits 10 (Nat.digits 10 n) := Eq.symm (Nat.ofDigits_digits 10 n)
    rw [hn] at this
    rw [Nat.ofDigits_eq_sum_mapIdx] at this
    simp at this
    rw [this]
    ring
  
  --Every digits is 3 or 7. We check each case.
  have ha0: a0 = 3 ∨ a0 = 7 := by apply h; simp [hn]
  have ha1: a1 = 3 ∨ a1 = 7 := by apply h; simp [hn]
  have ha2: a2 = 3 ∨ a2 = 7 := by apply h; simp [hn]
  have ha3: a3 = 3 ∨ a3 = 7 := by apply h; simp [hn]
  have ha4: a4 = 3 ∨ a4 = 7 := by apply h; simp [hn]
  have ha5: a5 = 3 ∨ a5 = 7 := by apply h; simp [hn]
  have ha6: a6 = 3 ∨ a6 = 7 := by apply h; simp [hn]
  
  rcases ha0 with a0e | a0e <;>
  rcases ha1 with a1e | a1e <;>
  rcases ha2 with a2e | a2e <;>
  rcases ha3 with a3e | a3e <;>
  rcases ha4 with a4e | a4e <;>
  rcases ha5 with a5e | a5e <;>
  rcases ha6 with a6e | a6e <;>
  simp [a0e,a1e,a2e,a3e,a4e,a5e,a6e] at eq <;>
  rw [eq] at d21h <;>
  norm_num at d21h <;>
  tauto


  --From right to left, we verify that these are exactly the solutions.
  intro h
  rcases h with ne | ne | ne | ne | ne | ne <;>
  simp [ne] <;>
  norm_num