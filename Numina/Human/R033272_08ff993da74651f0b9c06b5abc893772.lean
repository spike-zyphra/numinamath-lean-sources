import Mathlib

/- What is the smallest positive integer $t$ such that there exist integers
  $x_{1}, x_{2}, \ldots, x_{t}$ with $ x_{1}^{3}+x_{2}^{3}+\cdots+x_{t}^{3}=2002^{2002}$?
  Answer: $4$. -/
theorem number_theory_25102 :
    IsLeast {t : ℕ | 0 < t ∧ ∃ x : Fin t → ℤ, ∑ i : Fin t, (x i)^3 = 2002^2002} 4 := by
  constructor
  · simp only [Set.mem_setOf_eq, Nat.ofNat_pos, true_and]
    -- verify that (10^3 + 10^3 + 1^3 + 1^3)*(2000^667)^3 = 2002^2002
    let x (k : Fin 4) : ℤ := match k with
      | 0 => 10
      | 1 => 10
      | 2 => 1
      | 3 => 1
    use x * 2002 ^ 667
    native_decide
  · -- We consider the given equation $Mod 9$

    -- LHS: note that the cube of an integer is equal to $0$, $1$ or $8$ when considered $Mod 9$.
    have hcube (x : ℤ) : (x ^ 3 : ZMod 9) = 0 ∨ (x ^ 3 : ZMod 9) = 1 ∨ (x ^ 3 : ZMod 9) = 8 := by
      -- The three cases correspond to the remainder when divided by $3$
      rcases (by omega : (3 ∣ x) ∨ (3 ∣ x + 1) ∨ (3 ∣ x + 2) ) with h | h | h
      · left; norm_cast
        obtain ⟨k, hk⟩  := h
        have : x ^ 3 = 9 * (3 * k ^ 3) := by rw [hk, mul_pow, ← mul_assoc]; norm_num
        rw [this]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (9 * (3 * k ^ 3)) 9).mpr (by omega)
      · right; right; norm_cast
        obtain ⟨k, hk⟩ := h
        have : x ^ 3 = 9 * (3 * k ^ 3 - 3 * k ^ 2 + k) - 1 := calc
          _ = (3 * k - 1) ^ 3 := by rw [show 3 * k - 1 = x by omega]
          _ = 27 * k ^ 3 - 27 * k ^ 2 + 9 * k - 1 := by ring
          _ = _ := by omega
        refine (ZMod.intCast_eq_intCast_iff_dvd_sub (x ^ 3) 8 9).mpr (by omega)
      · right; left; norm_cast
        obtain ⟨k, hk⟩ := h
        have : x ^ 3 = 9 * (3 * k ^ 3 - 6 * k ^ 2 + 4 * k) - 8 := calc
          _ = (3 * k - 2) ^ 3 := by rw [show 3 * k - 2 = x by omega]
          _ = 27 * k ^ 3 - 54 * k ^ 2 + 36 * k - 8 := by ring
          _ = _ := by omega
        refine (ZMod.intCast_eq_intCast_iff_dvd_sub (x ^ 3) 1 9).mpr (by omega)

    -- RHS: observe that $2002^{2002} \equiv 4^{2002}=4 \cdot 64^{667} \equiv 4(\bmod 9)$
    have rhs : (2002 ^ 2002 : ZMod 9) = 4 := by native_decide

    -- The above implies that each case $t<4$ is impossible
    intro n hn; rw [Set.mem_setOf_eq] at hn
    by_contra hc; push_neg at hc

    interval_cases n
    · exact Nat.not_succ_le_zero 0 hn.1
    · obtain ⟨_, ⟨x, hx⟩⟩ := hn
      replace hx := congrArg (fun (z : ℤ) ↦ (z : ZMod 9)) hx
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
        Int.cast_pow, Int.cast_ofNat] at hx
      rw [rhs] at hx
      have h : ((x 0) ^ 3 : ZMod 9) ≠ 4 := by
        rcases (hcube (x 0)) with h0 | h0 | h0
        all_goals
          · rw [h0]; decide
      exact h hx
    · obtain ⟨_, ⟨x, hx⟩⟩ := hn
      replace hx := congr_arg (fun (z : ℤ) ↦ (z : ZMod 9)) hx
      simp only [Fin.sum_univ_two, Fin.isValue, Int.cast_add, Int.cast_pow, Int.cast_ofNat,
        rhs] at hx
      have h : ((x 0) ^ 3 + (x 1) ^ 3 : ZMod 9) ≠ 4 := by
        rcases (hcube (x 0)) with h0 | h0 | h0
        all_goals
        · rcases (hcube (x 1)) with h1 | h1 | h1
          all_goals
          · rw [h0, h1]; decide
      exact h hx
    · obtain ⟨_, ⟨x, hx⟩⟩ := hn
      replace hx := congr_arg (fun (z : ℤ) ↦ (z : ZMod 9)) hx
      simp only [Int.cast_sum, Int.cast_pow, Int.cast_ofNat, Fin.sum_univ_three, Fin.isValue,
        Int.cast_add, rhs] at hx
      have h : ((x 0) ^ 3 + (x 1) ^ 3 + (x 2) ^ 3 : ZMod 9) ≠ 4 := by
        rcases (hcube (x 0)) with h0 | h0 | h0
        all_goals
        · rcases (hcube (x 1)) with h1 | h1 | h1
          all_goals
          · rcases (hcube (x 2)) with h2 | h2 | h2
            all_goals
            · rw [h0, h1, h2]; decide
      exact h hx
