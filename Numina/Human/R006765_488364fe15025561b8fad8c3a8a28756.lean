import Mathlib

inductive Board (N k : ℕ) : Multiset ℕ → ℕ → Prop where
| initial : Board N k (Multiset.replicate N k) 0
| step x y S P : Board N k (insert x (insert y S)) P → Board N k (insert (x + y) S) (P + x * y)
open Board

-- The sum of numbers on board is invariant
lemma lemma_S_1 (board : Board N k S P) : S.sum = N * k := by
  induction board with
  | initial => simp
  | step x y S P board ih =>
      simp at *
      omega

-- Therefore, the last number on board is N * k
lemma lemma_S (board : Board N k {s} P) : s = N * k := by
  have := lemma_S_1 board
  simp at this
  assumption

-- The square sum of numbers on board minus 2 * condy count is invariant
lemma lemma_P_1 (board : Board N k S P) : (S.map (. ^ 2)).sum = 2 * P + N * k ^ 2 := by
  induction board with
  | initial => simp
  | step x y S P board ih =>
      simp at *
      ring_nf at *
      omega

-- Therefore, the total candy count is a fixed number N * (N - 1) / 2 * k ^ 2, and is thus the greatest possible number
lemma lemma_P (board : Board N k {s} P) (hN : 1 ≤ N := by omega) : P = N * (N - 1) / 2 * k ^ 2 := by
  have := lemma_P_1 board
  simp at this
  -- Since the last number in board is known, so is its square
  rw [lemma_S board] at this
  ring_nf at this
  have : N ^ 2 * k ^ 2 - N * k ^ 2 = P * 2 := by omega
  rw [←Nat.sub_mul, pow_two] at this
  have : (N * N - N) * k ^ 2 / 2 = P := by omega
  nth_rw 3 [←mul_one N] at this
  rw [←Nat.mul_sub, mul_comm, Nat.mul_div_assoc, mul_comm] at this
  simp [this]
  . by_cases h : 2 ∣ N
    . apply Nat.dvd_trans h
      apply dvd_mul_right
    . have h : 2 ∣ N - 1 := by omega
      apply Nat.dvd_trans h
      apply dvd_mul_left

-- It remains to prove that there exists at least one operation sequence that ends with one number on board.
-- This is mentally trivial but requires some work.
-- We show a stronger version that we can decrease any amount from the count of numbers on board with some operation sequence
lemma lemma_board_1 (N k m : ℕ) (hm : m < N := by omega) : ∃ S P, Board N k S P ∧ S.card = N - m := by
  -- Let m denote the amount we want to decrease. Use induction on m.
  induction m with
  | zero =>
      -- When m = 0, it's just the initial state.
      repeat constructor
      simp
  | succ m ih =>
      obtain ⟨S, P, board, h⟩ := ih
      -- We know S.card > 2 so we extract x and y from S
      obtain ⟨x, hx⟩ := by
        apply Multiset.exists_mem_of_ne_zero (s := S)
        rw [←Multiset.card_pos]
        omega
      obtain ⟨y, hy⟩ := by
        apply Multiset.exists_mem_of_ne_zero (s := S.erase x)
        rw [←Multiset.card_pos]
        rw [Multiset.card_erase_of_mem hx]
        simp
        omega
      -- And we just add x and y
      use insert (x + y) ((S.erase x).erase y)
      use P + x * y
      constructor
      . constructor
        have : insert x (insert y ((S.erase x).erase y)) = S := by
          simp
          rw [Multiset.cons_erase hy, Multiset.cons_erase hx]
        rw [this]
        assumption
      . simp
        rw [Multiset.card_erase_of_mem hy, Multiset.card_erase_of_mem hx]
        simp
        omega

-- Combined with prevoius lemmas, we know the constructed operation sequence ends with N * k on board
-- and a candy count of N * (N - 1) / 2 * k ^ 2
def lemma_board (N k : ℕ) (hN : 1 ≤ N := by omega) : Board N k {N * k} (N * (N - 1) / 2 * k ^ 2) := by
  obtain ⟨S, P, board, h⟩ := lemma_board_1 N k (N - 1)
  obtain ⟨s, hs⟩ : ∃ a, S = {a} := by
    rw [←Multiset.card_eq_one]
    omega
  subst S
  rw [lemma_S board, lemma_P board] at board
  exact board

/- Let $N$ be an integer greater than 1 and $k$ be a natural number. Suppose $N$ numbers, all equal to $k$, are initially written on a board. In each step, two numbers $x$ and $y$ are chosen arbitrarily from the numbers on the board, erased, and their sum $x+y$ is written on the board. Karlson eats a number of candies equal to the product $x \cdot y$. This process is repeated $N-1$ times, at which point only one number remains on the board. Determine the maximum possible total number of candies Karlson could have eaten. Show that this maximum is $\frac{N(N-1)}{2} k^2$. -/
theorem number_theory_640918 {N : ℕ} (hN : N > 1) (k : ℕ) :
    IsGreatest {P | ∃ s, Board N k {s} P} (N * (N - 1) / 2 * k ^ 2) := by
  constructor
  . simp
    constructor
    exact lemma_board N k
  . simp [upperBounds]
    intro P s board
    rw [lemma_P board]
