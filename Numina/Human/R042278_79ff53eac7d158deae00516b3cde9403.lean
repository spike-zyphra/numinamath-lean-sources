import Mathlib

/- Let $T_{k}=k-1$ for $k=1,2,3,4$ and
$$ T_{2 k-1}=T_{2 k-2}+2^{k-2}, \quad T_{2 k}=T_{2 k-5}+2^{k} \quad(k \geq 3) $$
Show that for all $k$,
$$ 1+T_{2 n-1}=\left[\frac{12}{7} 2^{n-1}\right] \quad \text { and } \quad 1+T_{2 n}=\left[\frac{17}{7} 2^{n-1}\right] $$
where $[x]$ denotes the greatest integer not exceeding $x$. -/
theorem other_24925 {T : ℕ → ℤ} (h1 : ∀ k, k ≤ 4 → T k = k - 1)
    (h2 : ∀ k ≥ 3, T (2 * k - 1) = T (2 * k - 2) + 2 ^ (k - 2))
    (h3 : ∀ k ≥ 3, T (2 * k) = T (2 * k - 5) + 2 ^ k) :
    ∀ n ≥ 1, 1 + T (2 * n - 1) = Int.floor ((12 / 7 : ℝ) * 2 ^ (n - 1)) ∧
    1 + T (2 * n) = Int.floor ((17 / 7 : ℝ) * 2 ^ (n - 1)) := by
  intro n hn
  -- We show manually the cases when `n ≤ 3` and then use two step induction for `3 < n`.
  obtain hc | hc : n = 1 ∨ 2 ≤ n := by omega
  · -- Case `n = 1`
    have h : T 1 = 0 := h1 1 (by omega)
    have h' : T 2 = 1 := h1 2 (by omega)
    rw [hc, h, h']
    norm_num
  · -- Case `n ≥ 3`
    obtain ⟨k, hk⟩ : ∃ k, n = 2 + k := by
      exact Nat.exists_eq_add_of_le hc
    rw [hk]
    clear hk hn hc n
    -- We use two step induction on `n` starting from `n = 2`.
    induction k using Nat.twoStepInduction with
    | zero => -- Case `n = 2`
        have h : T 3 = 2 := h1 3 (by omega)
        have h' : T 4 = 3 := h1 4 (by omega)
        rw [h, h']
        norm_num
    | one => -- Case `n = 3`
        constructor
        · rw [h2 3 (by norm_num) , h1 4 (by omega)]
          norm_num
        · rw [h3 3 (by omega), h1 1 (by omega)]
          norm_num
    | more k ih ih' =>
      -- Inductive step, using the given formulae in order to reduce to known cases.
      constructor
      · calc
          _ = 1 + T (2 * (4 + k) - 2) + 2 ^ (4 + k - 2) := by
            rw [show 2 * (2 + (k + 2)) - 1 = 2 * (4 + k) - 1 by omega]
            rw [h2 (4 + k) (by omega), add_assoc]
          _ = 1 + T (2 * (3 + k)) + 2 ^ (2 + k) := by
            rw [show 4 + k - 2 = 2 + k by omega, show 2 * (4 + k) - 2 = 2 * (3 + k) by omega]
          _ = ⌊(17 / 7 : ℝ) * 2 ^ (2 + k)⌋ + 2 ^ (2 + k) := by
            rw [show 2 * (3 + k) = 2 * (2 + (k + 1)) by omega, ih'.2]
            exact rfl
          _ = _ := by
            have := Int.floor_add_nat ((17 / 7 : ℝ) * 2 ^ (2 + k)) (2 ^ (2 + k))
            push_cast at this
            rw [← this, show 2 + (k + 2) - 1 = 2 + (k + 1) by omega]
            congr
            ring
      · calc
          _ = 1 + T (2 * (4 + k) - 5) + 2 ^ (4 + k) := by
            rw [show 2 * (2 + (k + 2)) = 2 * (4 + k) by omega]
            rw [h3 (4 + k) (by omega), add_assoc]
          _ = 1 + T (2 * (2 + k) - 1) + 2 ^ (4 + k) := by
            rw [show 2 * (4 + k) - 5 = 2 * (2 + k) - 1 by omega]
          _ = ⌊(12 / 7 : ℝ) * 2 ^ (1 + k)⌋ + 2 ^ (4 + k) := by
            rw [ih.1, show 2 + k - 1 = 1 + k by omega]
          _ = _ := by
            have := Int.floor_add_nat ((12 / 7 : ℝ) * 2 ^ (1 + k)) (2 ^ (4 + k))
            push_cast at this
            rw [← this, show 2 + (k + 2) - 1 = 3 + k by omega]
            congr
            ring
