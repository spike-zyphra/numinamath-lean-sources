import Mathlib

theorem number_theory_230706 :
    IsGreatest {k : ℕ | ∃ X Y Z W : ℕ, 0 < X ∧ 0 < Y ∧ 0 < Z ∧ 0 < W ∧ k = [X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].countP (fun x => Odd x)} 4 := by
  constructor
  · -- Show 4 is in the set
    use 1, 3, 2, 4
    all_goals
    native_decide
  · -- Show that any element in the set is ≤ 4
    intro k hk
    rcases hk with ⟨X, Y, Z, W, hX, hY, hZ, hW, hk⟩
    have h1 : k = [X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].countP (fun x => Odd x) := by
      exact hk
    have h2 : [X + Y, X + Z, X + W, Y + Z, Y + W, Z + W].countP (fun x => Odd x) ≤ 4 := by
      have h3 : (X % 2 = 0 ∨ X % 2 = 1) := by omega
      have h4 : (Y % 2 = 0 ∨ Y % 2 = 1) := by omega
      have h5 : (Z % 2 = 0 ∨ Z % 2 = 1) := by omega
      have h6 : (W % 2 = 0 ∨ W % 2 = 1) := by omega
      rcases h3 with (h3 | h3) <;> rcases h4 with (h4 | h4) <;> rcases h5 with (h5 | h5) <;> rcases h6 with (h6 | h6) <;> 
        simp [Nat.odd_iff, Nat.add_mod, h3, h4, h5, h6] <;> try native_decide
    linarith