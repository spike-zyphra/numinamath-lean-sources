import Mathlib

/-John counts up from 1 to 13, and then immediately counts down again to 1, and then back up to 13, and so on, alternately counting up and down: \begin{align*}
&(1, 2, 3,4,5,6,7,8,9,10,11,12,13,\\
&\qquad\qquad12,11,10,9,8,7,6,5,4,3,2,1,2,3,4,\ldots ).
\end{align*} What is the $5000^{\text{th}}$ integer in his list?-/
theorem algebra_20019 (f : ℕ → ℕ) (h0 : f 0 = 1) (hn : ∀ n : ℕ, f (n + 1) = if ((n / 12) % 2 = 0) then f n + 1 else f n - 1) : f 4999 = 8 := by
  -- show that the sequence repeats itself every 24 elements
  have rep (n : ℕ) : f (n + 24) = f n := by
    induction n with -- by induction
    | zero => -- when n = 0
      simp
      rw [h0]
      simp_rw [hn]
      simp
      exact h0
    | succ m hm => -- when m satisfied, show the case of m + 1
      -- first show that (m + 24) / 12 % 2 = 0 equal to m / 12 % 2 = 0
      have equiv₁ : (m + 24) / 12 % 2 = 0 ↔ m / 12 % 2 = 0 := by
        apply Iff.intro <;> intro hm1
        -- when (m + 24) / 12 % 2 = 0
        . rw [Nat.add_div] at hm1
          simp [show ¬12 ≤ m % 12 by simp; apply Nat.mod_lt; norm_num] at hm1
          exact hm1
          norm_num
        -- similar to the case of above
        . rw [Nat.add_div]
          simp [show ¬12 ≤ m % 12 by simp; apply Nat.mod_lt; norm_num]
          exact hm1
          norm_num
      -- calculate that f (m + 1 + 24) = f (m + 1) by definition
      calc
        f (m + 1 + 24) = f (m + 24 + 1) := by norm_num
        _ = if ((m + 24) / 12 % 2 = 0) then f (m + 24) + 1 else f (m + 24) - 1 := by rw [hn]
        _ = if (m / 12 % 2 = 0) then f (m + 24) + 1 else f (m + 24) - 1 := by congr 1; rw [equiv₁]
        _ = if (m / 12 % 2 = 0) then f m + 1 else f m - 1 := by rw [hm]
        _ = f (m + 1) := by rw [<-hn]
  -- show that for any m ∈ ℕ, f (n + 24 * m) = f n
  have rep₂ (n m : ℕ) : f (n + 24 * m) = f n := by
    induction m with
    -- when m = 0
    | zero =>
      norm_num
    -- when m satisfied, show the m + 1
    | succ m hm =>
      calc
        f (n + 24 * (m + 1)) = f (n + 24 * m + 24) := by ring_nf
        _ = f (n + 24 * m) := by rw [rep]
        _ = f n := by rw [hm]
  -- show that f (7) = 8
  have h7 : f 7 = 8 := by 
    simp_rw [hn]
    simp
    exact h0
  -- calculate f 4999 by repitivity.
  calc
    f 4999 = f (7 + 24 * 208) := by ring_nf
    _ = f 7 := by rw [rep₂]
    _ = 8 := by rw [h7]