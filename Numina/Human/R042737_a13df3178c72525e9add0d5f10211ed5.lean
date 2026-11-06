import Mathlib

/-
Find all positive integers $n$ for which

$$
3 x^{n}+n(x+2)-3 \geq n x^{2}
$$

holds for all real numbers $x$.
-/
theorem inequalities_239559 {n : ℕ} : (∀ x : ℝ, 3 * x ^ n + n * (x + 2) - 3 ≥ n * x ^ 2) ↔ Even n := by
  constructor <;> intro h
  · -- If $n$ is odd, the for $x=-1$
    -- the left hand side of the inequality equals $n-6$ while the right hand side is $n$.
    -- So the inequality is not true for $x=-1$ for any odd $n$.
    by_contra hodd
    simp at hodd
    obtain h := h (-1)
    simp [hodd] at h
    linarith
  · -- So now assume that $n$ is even. Since $|x| \geq x$, it is enough to prove $3 x^{n}+2 n-3 \geq n x^{2}+n|x|$ for all $x$
    suffices h (x : ℝ) : 3 * x ^ n + 2 * n - 3 ≥ n * x ^ 2 + n * |x|
    · intro x
      obtain h := h x
      calc
        _ = 3 * x ^ n + 2 * ↑n - 3 + n * x := by ring
        _ ≥ n * x ^ 2 + n * |x| + n * x := by rel [h]
        _ = n * x ^ 2 + n * (|x| + x) := by ring
        _ ≥ n * x ^ 2 + n * 0 := by rel [show |x| + x ≥ 0 by rw [add_comm]; apply add_abs_nonneg]
        _ = n * x ^ 2 := by ring
    · -- or equivalently that $3 x^{n}+(2 n-3) \geq n x^{2}+n x$ for $x \geq 0$.
      wlog hx : x ≥ 0 with H
      · simp at hx
        let x' := -x
        have : x' ≥ 0 := by simp [x']; linarith
        apply H h x' at this
        simp [x', h] at this
        exact this
      · by_cases hn : n = 0
        · -- n = 0 => trivial
          simp [hn]
        · -- n ≠ 0
          have hn' : n ≥ 2 := by
            by_contra hn'
            simp at hn'
            interval_cases n
            · simp at hn
            · simp at h
          simp [show |x| = x by apply abs_of_nonneg hx]
          -- apply the am-gm inequality
          have h1 : 2 * x ^ n + (n - 2) ≥ n * x ^ 2 := by
            let s := Finset.range n
            let w (i : ℕ) := 1 / (n : ℝ)
            let z (i : ℕ) : ℝ := if i < 2 then x ^ n else (1 : ℝ)
            have hw : ∀ i ∈ s, 0 ≤ w i := by simp [w]
            have hw' : ∑ i ∈ s, w i = 1 := by
              simp [w, s]
              rw [mul_inv_cancel₀]
              simp [hn]
            have hz : ∀ i ∈ s, 0 ≤ z i := by
              simp [z, s]
              intro i _
              apply ite_nonneg
              · apply pow_nonneg hx
              · norm_num
            obtain h := Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz
            simp [s, w, z] at h
            rw [Finset.sum_ite, Finset.prod_ite] at h
            have h1 : Finset.filter (fun x ↦ x < 2) (Finset.range n) = {0, 1} := by
              ext i
              simp
              constructor <;> intro h
              · obtain h := h.2
                interval_cases i
                all_goals simp
              · rcases h with h | h
                · simp [h]; exact Nat.zero_lt_of_ne_zero hn
                · simp [h]; exact hn'
            have h2 : Finset.filter (fun x ↦ 2 ≤ x) (Finset.range n) = Finset.Icc 2 (n - 1) := by
              ext i
              simp
              constructor <;> intro h
              · constructor
                · exact h.2
                · apply Nat.le_sub_one_of_lt h.1
              · constructor
                · apply Nat.lt_of_le_sub_one
                  · exact Nat.zero_lt_of_ne_zero hn
                  · exact h.2
                · exact h.1
            simp [h1, h2] at h
            rw [←Real.rpow_natCast _ n, ←Real.rpow_mul, mul_inv_cancel₀, Real.rpow_one, Nat.cast_sub, Nat.cast_sub] at h
            · simp at h
              calc
                _ = (2 * ((↑n)⁻¹ * x ^ ↑n) + (↑n - 1 - 1) * (↑n)⁻¹) * n := by field_simp; ring
                _ ≥ x ^ 2 * n := by rel [h]
                _ = _ := by ring
            · exact Nat.one_le_of_lt hn'
            · exact Nat.le_sub_one_of_lt hn'
            · exact Nat.cast_ne_zero.mpr hn
            · exact hx
          -- apply the am-gm inequality
          have h2 : x ^ n + (n - 1) ≥ n * x := by
            let s := Finset.range n
            let w (i : ℕ) := 1 / (n : ℝ)
            let z (i : ℕ) : ℝ := if i < 1 then x ^ n else (1 : ℝ)
            have hw : ∀ i ∈ s, 0 ≤ w i := by simp [w]
            have hw' : ∑ i ∈ s, w i = 1 := by
              simp [w, s]
              rw [mul_inv_cancel₀]
              simp [hn]
            have hz : ∀ i ∈ s, 0 ≤ z i := by
              simp [z, s]
              intro i _
              apply ite_nonneg
              · apply pow_nonneg hx
              · norm_num
            obtain h := Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz
            simp [s, w, z] at h
            rw [Finset.sum_ite] at h
            simp [show 0 < n by exact Nat.zero_lt_of_ne_zero hn] at h
            have h2 : Finset.filter (fun x ↦ ¬ x = 0) (Finset.range n) = Finset.Icc 1 (n - 1) := by
              ext i
              simp
              constructor <;> intro ⟨h1, h2⟩
              · constructor
                · exact Nat.one_le_iff_ne_zero.mpr h2
                · apply Nat.le_sub_one_of_lt h1
              · constructor
                · apply Nat.lt_of_le_sub_one
                  · exact Nat.zero_lt_of_ne_zero hn
                  · exact h2
                · exact Nat.not_eq_zero_of_lt h1
            simp [h1, h2] at h
            rw [←Real.rpow_natCast _ n, ←Real.rpow_mul, mul_inv_cancel₀, Real.rpow_one, Nat.cast_sub] at h
            · simp at h
              calc
                _ = ((↑n)⁻¹ * x ^ n + (↑n - 1) * (↑n)⁻¹) * n := by field_simp
                _ ≥ x * n := by rel [h]
                _ = _ := by ring
            · exact Nat.one_le_of_lt hn'
            · exact Nat.cast_ne_zero.mpr hn
            · exact hx
          -- Adding (1) and (2) yields the claim.
          calc
            _ ≤ 2 * x ^ n + (n - 2) + (x ^ n + (n - 1)) := by rel [h1, h2]
            _ = _ := by ring
