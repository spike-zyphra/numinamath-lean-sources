import Mathlib

/-
Let `b` be an integer representing the base, and assume `b > 2`.
Let `N₁` be the number whose base `b` representation is `(b-1)1`, i.e., `(b-1) * b + 1`.
Let `N₂` be the number whose base `b` representation is `(b-2)2`, i.e., `(b-2) * b + 2`.
Compute the difference `N₁ - N₂` and show that the result,
when expressed in base `b`, is represented by the single digit `b-1`.
-/
theorem integer_base_problem (hb : b > 2) :
  -- We state the two parts of the problem as a logical conjunction (∧).
  -- Part 1: The value of the subtraction.
  -- Part 2: The base `b` representation of that value.
  -- We use `let` to give readable names to the numbers without a top-level `def`.
  let N₁ := (b - 1) * b + 1;
  let N₂ := (b - 2) * b + 2;
  (N₁ - N₂ = b - 1) ∧ (Nat.digits b (N₁ - N₂) = [b - 1]) := by

  -- We use a `have` statement with the `calc` tactic to prove the result of the subtraction.
  -- This makes the algebraic manipulation explicit and demonstrates how the `hb : b > 2`
  -- constraint is used to handle natural number subtraction correctly.
  have h_diff : ((b - 1) * b + 1) - ((b - 2) * b + 2) = b - 1 := by
    calc
      -- Start with the original expression
      ((b - 1) * b + 1) - ((b - 2) * b + 2)
      -- Step 1: Rewrite (b-1) as (b-2)+1. This is valid because `hb : b > 2` implies 2 <= b.
      _ = (((b - 2) + 1) * b + 1) - ((b - 2) * b + 2) := by
          congr
          omega
      -- Step 2: Distribute the multiplication by `b` over the addition.
      _ = ((b - 2) * b + b + 1) - ((b - 2) * b + 2) := by
          rw [add_mul, one_mul]
      -- Step 3: Rearrange terms using commutativity and associativity of addition
      -- to isolate the common part `(b-2)*b`.
      _ = ((b + 1) + (b - 2) * b) - (2 + (b - 2) * b) := by omega
      -- Step 4: Apply the subtraction rule `(a+c)-(b+c) = a-b`.
      -- This is `Nat.add_sub_add_right` in Lean, and it is applicable because
      -- `2 + (b-2)*b <= (b+1) + (b-2)*b`, which holds since `2 <= b+1`.
      _ = (b + 1) - 2 := by
          rw [Nat.add_sub_add_right]
      -- Step 5: Final calculation, proving (b+1)-2 = b-1.
      _ = b - 1 := by
          -- To prove `x-y = z` for natural numbers, we can prove `x = z+y`.
          apply Nat.sub_eq_of_eq_add
          -- The goal becomes `b+1 = (b-1)+2`.
          rw [add_comm] -- `b+1 = 2+(b-1)`
          omega

  -- The rest of the proof proceeds as before.
  -- The goal is a conjunction `P ∧ Q`. We use `And.intro` to prove `P` and `Q` separately.
  apply And.intro

  -- Goal 1: Prove the first part of the conjunction.
  -- This is exactly what we proved in our `calc` block `h_diff`.
  . exact h_diff

  -- Goal 2: Prove the second part of the conjunction.
  . -- We use our proof `h_diff` to rewrite the expression inside `Nat.digits`.
    rw [h_diff]
    -- The goal is now `Nat.digits b (b - 1) = [b - 1]`.
    -- The proof for this part remains the same.
    rw [Nat.digits_def' (by linarith) ]
    -- Since b > 2, we know b-1 < b.
    have h_lt_b : b - 1 < b := Nat.sub_lt (by linarith) (by simp)
    -- This simplifies the mod  and div operations.
    rw [Nat.mod_eq_of_lt h_lt_b]
    rw [Nat.div_eq_of_lt h_lt_b]
    -- The goal becomes `[b-1] = (b-1) :: Nat.digits b 0`.
    -- The digits of 0 is an empty list.
    rw [Nat.digits_zero]
    -- The goal `[b-1 ] = (b-1) :: []` is true by definition.
    omega
