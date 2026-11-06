import Mathlib
open Real Finset Nat List
noncomputable section

-- Lemma: Prove that the square of an odd number modulo $8$ equals $1$.
lemma odd_square_mod_eight (k : ℕ) (hk : k % 2 = 1) : k^2 % 8 = 1 := by
  -- Odd number $k$ eq $2m + 1$.
  have h_k_form : ∃ m, k = 2 * m + 1 := by
    exists (k / 2)
    rw [← Nat.div_add_mod k 2, hk]
    omega
  rcases h_k_form with ⟨m, h_k⟩
  -- Compute $k^2 = (2m + 1)^2$.
  have h_k_square : k^2 = 4 * m * (m + 1) + 1 := by
    rw [h_k, pow_two]
    simp [mul_add, add_mul]
    ring
  have h_m_even : (m * (m + 1)) % 2 = 0 := by
    exact Nat.even_iff.mp (Nat.even_mul_succ_self m)
  -- Prove $4 * m * (m + 1)$ is a multiple of $8$.
  have h_4m : 4 * (m * (m + 1)) = 8 * (m * (m + 1) / 2) := by
    have : m * (m + 1) = 2 * (m * (m + 1) / 2) := by
      rw [← Nat.div_add_mod (m * (m + 1)) 2]
      simp [h_m_even]
    conv =>
      left;rw [this]
    rw [← mul_assoc]
    simp
  -- From $k^2 = 8 * p + 1$, deduce $k^2 % 8 = 1$.
  have h_k_mod : k^2 = 8 * (m * (m + 1) / 2) + 1 := by
    rw [h_k_square]
    simp
    rw [mul_assoc]
    exact h_4m
  have h_mod : k^2 % 8 = 1 := by
    rw [h_k_mod]
    omega
  exact h_mod

/-A finger counting game follows a repeating pattern. The fingers are counted starting with the 1st, 2nd, 3rd, and so on. The sequence of fingers touched is Pinky, Ring, Middle, Index, Thumb, then Index, Middle, Ring. This 8-step sequence (Pinky, Ring, Middle, Index, Thumb, Index, Middle, Ring) then repeats. We assign a numerical value to each finger: Pinky=0, Ring=1, Middle=2, Index=3, and Thumb=4.
Let $k$ be an odd positive integer. Determine the numerical value of the finger corresponding to the $k^2$-th count in this sequence. Show the answer is 0.-/
theorem number_theory_635376 (k : ℕ) (hk : k % 2 = 1) :
    [0, 1, 2, 3, 4, 3, 2, 1].get! ((k^2 - 1) % 8) = 0 := by
  -- Prove $k^2 % 8 = 1$ by the lemma
  have h_k2_mod : k^2 % 8 = 1 := by
    apply odd_square_mod_eight k hk
  -- Derive $(k^2 - 1) % 8 = 0$
  have h_index_mod : (k^2 - 1) % 8 = 0 := by
    exact Nat.sub_mod_eq_zero_of_mod_eq h_k2_mod
  -- Compute the index.
  have h_index : (k^2 - 1) % 8 = 0 := by
    exact h_index_mod
  -- Verify $[0, 1, 2, 3, 4, 3, 2, 1][0] = 0$.
  have h_value : [0, 1, 2, 3, 4, 3, 2, 1].get! 0 = 0 := by
    simp
  -- Conclusion.
  rw [h_index, h_value]
