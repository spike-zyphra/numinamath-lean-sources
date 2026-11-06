import Mathlib

/- Let $b$ be an integer such that $b \ge 2$.
Let $N_1$ be the number represented in base $b$ by the list of digits $[1,1,1]$ (i.e., $N_1 = b^2+b+1$).
Let $N_2$ be the number represented in base $b$ by the list of digits $[1,0,1]$ (i.e., $N_2 = b^2+1$).
Let $N_3$ be the number represented in base $b$ by the list of digits $[1,0,0,1]$ (i.e., $N_3 = b^3+1$).
Let $P_1 = N_1 \cdot N_2$ and $P_2 = N_3 \cdot N_1 \cdot N_2$.

Define $L_{P1}$ and $L_{P2}$ as lists of digits.
If $b \ge 3$:
  Let $L_{P1} = [1,1,2,1,1]$ and $L_{P2} = [1,1,2,2,2,2,1,1]$.
If $b=2$:
  Let $L_{P1} = [1,0,0,0,1,1]$ and $L_{P2} = [1,0,0,1,1,1,0,1,1]$.

Show that $P_1$ is equal to the number represented in base $b$ by the list of digits $L_{P1}$, and $P_2$ is equal to the number represented in base $b$ by the list of digits $L_{P2}$. -/
theorem number_theory_635948 (b : ℕ) (hb : 2 ≤ b) (N₁ N₂ N₃ : ℕ) (hN₁ : b.digits N₁ = [1, 1, 1]) (hN₂ : b.digits N₂ = [1, 0, 1]) (hN₃ : b.digits N₃ = [1, 0, 0, 1]) (P₁ P₂ : ℕ) (hP₁ : P₁ = N₁ * N₂) (hP₂ : P₂ = N₃ * N₁ * N₂) :
    if 3 ≤ b then
        b.digits P₁ = [1, 1, 2, 1, 1] ∧ b.digits P₂ = [1, 1, 2, 2, 2, 2, 1, 1]
    else
        b.digits P₁ = [1, 1, 0, 0, 0, 1] ∧ b.digits P₂ = [1, 1, 0, 1, 1, 1, 0, 0, 1] := by
  -- Convert the digit representations to their numerical values using Nat.ofDigits
  apply_fun Nat.ofDigits b at hN₁ hN₂ hN₃
  -- Simplify the expressions using the fact that Nat.ofDigits and Nat.digits are inverses
  simp [Nat.ofDigits_digits, Nat.ofDigits] at hN₁ hN₂ hN₃
  -- Split the proof into two cases: b ≥ 3 and b = 2
  split_ifs with hb
  . constructor
    . -- Case 1: Prove P₁ = [1,1,2,1,1] in base b when b ≥ 3
      suffices H : P₁ = Nat.ofDigits b [1, 1, 2, 1, 1] by
          -- Convert back to digits to show equality
          apply_fun b.digits at H
          rwa [Nat.digits_ofDigits b (by omega) _ (by simp; omega) (by simp)] at H
      -- Simplify the expression and use ring to prove the equality
      simp [Nat.ofDigits, hP₁, hN₁, hN₂]
      ring
    . -- Case 2: Prove P₂ = [1,1,2,2,2,2,1,1] in base b when b ≥ 3
      suffices H : P₂ = Nat.ofDigits b [1, 1, 2, 2, 2, 2, 1, 1] by
          -- Convert back to digits to show equality
          apply_fun b.digits at H
          rwa [Nat.digits_ofDigits b (by omega) _ (by simp; omega) (by simp)] at H
      -- Simplify the expression and use ring to prove the equality
      simp [Nat.ofDigits, hP₂, hN₁, hN₂, hN₃]
      ring
  . -- Case 3: Handle the special case when b = 2
    obtain rfl : b = 2 := by omega
    -- Simplify the expressions for the binary case
    simp [hP₁, hP₂, hN₁, hN₂, hN₃]