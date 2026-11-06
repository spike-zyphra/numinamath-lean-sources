import Mathlib

def chessboard : Fin 8 → Fin 8 → ℕ
| r, c => 8 * r + c + 1

def is_black (r c : Fin 8) := (r + c) % 2 = 0

theorem number_theory_186971 :
    Set.ncard {p : Fin 8 × Fin 8 | is_black p.1 p.2 ∧ Odd (chessboard p.1 p.2)} = 16 := by
  have h1 : {p : Fin 8 × Fin 8 | is_black p.1 p.2 ∧ Odd (chessboard p.1 p.2)} = Finset.filter (fun p : Fin 8 × Fin 8 => ( (p.1 + p.2) % 2 = 0) ∧ (Odd (chessboard p.1 p.2)) ) (Finset.univ : Finset (Fin 8 × Fin 8)) := by
    ext ⟨r, c⟩
    simp [is_black]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide