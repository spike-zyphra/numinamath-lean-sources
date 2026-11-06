import Mathlib


/- Montrer qu'il existe une infinité de couples ( $\mathrm{m}, \mathfrak{n}$ ) d'entiers strictement positifs distincts tels que m ! n soit un carré parfait. -/
theorem number_theory_607425 :
    Set.Infinite {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ m ≠ n ∧ ∃ k, (Nat.factorial m) * (Nat.factorial n) = k ^ 2} := by 
  let S := {(m, n) : ℕ × ℕ | ∃ k : ℕ, m = k ^ 2 ∧ n = k ^ 2 - 1 ∧ k ≥ 2} -- Indeed, we consider the set $$S := \{(k², k² - 1) : k \ge 2\}$$
  have hS : S ⊆ {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ m ≠ n ∧ ∃ k, (Nat.factorial m) * (Nat.factorial n) = k ^ 2} := by 
    rintro ⟨m, n⟩ ⟨k, rfl, rfl, hk⟩
    have hk0 : k ^ 2 > 0 := Nat.pow_pos (Nat.zero_lt_of_lt hk) 
    have hk1 : k ^ 2 - 1 > 0 := by simpa using hk  
    refine ⟨hk0, hk1, ?_, ?_⟩ -- To prove that $S$ is a subset of $A$.
    · intro h -- $k^2 \neq k^2 - 1$
      rw [← Nat.Simproc.add_eq_le] at h 
      · simp at h 
      · exact hk0
    · use k * (k ^ 2 - 1).factorial -- To prove that $k^2! (k^2 - 1)!$ is a sqaure number. 
      calc 
        _ = k ^ 2 * (k ^ 2 - 1).factorial * (k ^ 2 - 1).factorial := by rw [Nat.mul_factorial_pred hk0]
        -- The crucial observation is made by writing out the factorials. Notice that \[ (k^2)! = k^2 \times (k^2 - 1)!.\] 
        _ = k ^ 2 * ((k ^ 2 - 1).factorial) ^ 2 := by simp only [mul_assoc, ← pow_two ((k ^ 2 - 1).factorial)]
        _ = _ := by ring 
      -- So $$\left(k^{2}\right)!\left(k^{2}-1\right)!=k^{2}\left(\left(k^{2}-1\right)!\right)^{2}=\left[k\left(k^{2}-1\right)!\right]^{2}$$
  have hS2 : Set.Infinite S := by 
    refine Set.infinite_of_forall_exists_gt ?_
    -- To establish the existence of infinitely many such pairs, 
    -- we observe that for every positive integer pairs $(x, y)$. 
    -- There exists $((x+y+2)², (x+y+2)²-1) \in S$ bigger than $(x, y)$. 
    rintro ⟨x, y⟩
    use ⟨(x + y + 2) ^ 2, (x + y + 2) ^ 2 - 1⟩ 
    constructor
    · simp [S] -- $((x+y+2)², (x+y+2)²-1) \in S$
    · apply Prod.mk_lt_mk_of_lt_of_le -- $((x+y+2)², (x+y+2)²-1) \in S$ bigger than $(x, y)$.
      · calc -- To prove that $(x + y + 2)² > x²$ 
          _ ≤ x ^ 2 := by simp [pow_two ,Nat.le_mul_self x] 
          _ < (x + y + 2) ^ 2 := by gcongr ; exact Nat.lt_add_of_pos_right (show y + 2 > 0 by simp) 
      · calc -- To prove that $(x + y + 2)² - 1 ≥ y²$
          _ ≤ y ^ 2 := by simp [pow_two ,Nat.le_mul_self y]
          _ ≤ (x + y + 2) ^ 2 - 1 := by 
            rw [Nat.le_sub_one_iff_lt (by simp), add_comm x y] ; gcongr 
            exact Nat.lt_add_of_pos_right (show x + 2 > 0 by simp)
  -- It implies that $S$ is infinite, then $A$ is finite.
  exact Set.Infinite.mono hS hS2 
 