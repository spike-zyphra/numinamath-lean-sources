import Mathlib

/- 17. You can choose four positive integers $X, Y, Z$ and $W$. What is the maximum number of odd numbers you can obtain from the six sums $X+Y, X+Z, X+W, Y+Z, Y+W$ and $Z+W$ ?
A 2
B 3
C 4
D 5
E 6 -/
theorem number_theory_230706 :
    IsGreatest {k : ℕ | ∃ X Y Z W : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ 0 < W ∧ k = [X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].countP (fun x => Odd x)} 4 := by
  constructor
  {
    -- We show that 4 is achievable.
    -- We can choose X = 1, Y = 1, Z = 2, W = 2.
    use 1, 1, 2, 2
    native_decide
  }
  -- Now we show that 4 is the maximum.
  rintro _ ⟨X, Y, Z, W, -, -, -, -, rfl⟩
  calc [X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].countP (fun x => Odd x)
    -- Odd x iff x = 1 in Zmod 2
    _ = [X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].countP ((fun x => x == 1) ∘ (Nat.cast : ℕ → ZMod 2)) := by
      congr
      ext x
      simp [beq_eq_decide, ZMod.eq_one_iff_odd]
    -- Map the list to Zmod 2
    _ = ([X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].map (Nat.cast : ℕ → ZMod 2)).countP (fun x => x == 1) := by rw [List.countP_map]
    _ = ([X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].map (Nat.cast : ℕ → ZMod 2)).count 1 := rfl
    -- Expand the casts
    _ = ([(X + Y : ZMod 2), X + Z, X + W, Y + Z, Y + W, Z + W]).count 1 := by simp
    _ ≤ 4 := by
      -- Generalize the variables x, y, z, w as the images of X, Y, Z, W under the map Nat.cast : ℕ → ZMod 2
      generalize (X : ZMod 2) = x, (Y : ZMod 2) = y, (Z : ZMod 2) = z, (W : ZMod 2) = w
      -- Move the variables under `∀`
      revert x y z w
      -- There are 2 ^ 4 = 16 possible values for x, y, z, w, we can use `native_decide` to check each case
      native_decide
