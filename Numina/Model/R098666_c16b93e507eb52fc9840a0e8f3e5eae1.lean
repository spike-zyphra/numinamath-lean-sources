import Mathlib

theorem algebra_11525 {a : ℕ → ℤ} (ha1 : a 1 = 1) (han : ∀ n > 0, a (n + 1) = 2 * a n + 1) :
    ∀ n > 0, a n = 2 ^ n - 1 := by
        intro n hn
        induction n with
        | zero => 
            exfalso
            exact Nat.lt_irrefl 0 hn
        | succ n ih =>
            cases n with
            | zero =>
                rw [ha1]
                norm_num
            | succ n =>
                have ih' := ih (Nat.succ_le_of_lt (Nat.succ_pos _))
                have h1 : a (n + 2) = 2 * a (n + 1) + 1 := han (n + 1) (by linarith)
                rw [h1]
                simp [ih']
                <;> ring_nf
                <;> norm_num
                <;> ring