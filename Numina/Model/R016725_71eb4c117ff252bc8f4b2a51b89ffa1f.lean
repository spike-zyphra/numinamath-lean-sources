import Mathlib

def chessboard : Fin 8 → Fin 8 → ℕ
| r, c => r * 8 + c + 1

def is_black (r c : Fin 8) := (r + c) % 2 = 0

theorem number_theory_610997 :
    Set.ncard {p : Fin 8 × Fin 8 | is_black p.1 p.2 ∧ Odd (chessboard p.1 p.2)} = 16 := by 
  simp [Set.ncard_eq_toFinset_card', Finset.filter, is_black, chessboard, Nat.odd_iff]
  <;> native_decide