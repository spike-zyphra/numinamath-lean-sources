import Mathlib
open Finset Set Nat  
noncomputable section

-- Define the number of ways to place pawns.
def place_pawns (n : ℕ) : ℕ := (n + 1) ^ 8

/-How many ways are there to place pawns on an $8 \times 8$ chessboard, so that there is at most 1 pawn in each horizontal row? Express your answer in the form $p_{1}^{e_{1}} \cdot p_{2}^{e_{2}} \cdots$, where the $p_{i}$ are distinct primes and the $e_{i}$ are positive integers.-/
theorem combinatorics_608712 :
    (place_pawns 8).factorization = Finsupp.single 3 16 := by
  -- $0$ pawns per row: $1$ way.
  have h_zero : 1 = 1 := by rfl
  -- $1$ pawn per row: $8$ ways.
  have h_one : card (univ : Finset (Fin 8)) = 8 := by simp [card_fin]
  -- Total ways per row: $1 + 8 = 9$
  have h_row : 1 + 8 = 9 := by norm_num
  -- Total ways for $8$ rows: $9^8$.
  have h_total : place_pawns 8 = 9 ^ 8 := by
    rw [place_pawns, h_row]
  have h_nine : 9 = 3 ^ 2 := by norm_num
  have h_factor : (9 : ℕ) ^ 8 = 3 ^ 16 := by
    have : 2 * 8 = 16 := by norm_num
    rw [h_nine, ← pow_mul, this]
  -- Factorization of $3^16$ is Finsupp.single $3$ $16$.
  have h_factorization : (3 ^ 16 : ℕ).factorization = Finsupp.single 3 16 := by
    rw [Nat.factorization_pow]
    have : (3 : ℕ).factorization = Finsupp.single 3 1 := by
      apply Nat.Prime.factorization
      exact Nat.prime_three
    rw [this]
    simp [Finsupp.single_smul]
  -- Conclusion.
  rw [h_total, h_factor, h_factorization]
