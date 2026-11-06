import Mathlib

open Finset Real

theorem algebra_3890 {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ range n, (6 / 9) * (10 ^ (i + 1) - 1) = (20 / 27) * (10 ^ n - 1) - (2 * n / 3) := by 
        induction n with 
        | zero =>
            linarith 
        | succ n ih =>
            cases n with 
            | zero =>
                norm_num 
            | succ n =>
                rw [sum_range_succ, ih (by linarith)]
                field_simp
                ring_nf
                <;> omega