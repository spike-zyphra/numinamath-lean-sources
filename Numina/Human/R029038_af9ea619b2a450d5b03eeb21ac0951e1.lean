import Mathlib

open Finset

/- For positive integers $a$, $b$, and $c$ with $a < b < c$, consider collections of postage stamps in denominations $a$, $b$, and $c$ cents that contain at least one stamp of each denomination. If there exists such a collection that contains sub-collections worth every whole number of cents up to $1000$ cents, let $f(a, b, c)$ be the minimum number of stamps in such a collection. Find the sum of the three least values of $c$ such that $f(a, b, c) = 97$ for some choice of $a$ and $b$. -/
theorem number_theory_25462 {f : ℕ → ℕ → ℕ → ℕ}
    (hf : ∀ a b c, f a b c = sInf {n | ∃ x y z, n = x + y + z ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧
      ∀ i ∈ Icc 1 1000, ∃ x' y' z', i = x'*a + y'*b + z'*c ∧ x' ≤ x ∧ y' ≤ y ∧ z' ≤ z}) :
    (Nat.nth {c | ∃ a b, 0 < a ∧ a < b ∧ b < c ∧ f a b c = 97} 0) +
    (Nat.nth {c | ∃ a b, 0 < a ∧ a < b ∧ b < c ∧ f a b c = 97} 1) +
    (Nat.nth {c | ∃ a b, 0 < a ∧ a < b ∧ b < c ∧ f a b c = 97} 2) = 188 := by
  -- Prove an auxiliary lemma: k * (x / k) = x - x % k for all natural numbers x and k.
  have mul_div_self (x k : ℕ) : k * (x / k) = x - x % k := by
    nth_rw 2 [← Nat.div_add_mod x k]
    omega
  -- Prove an auxiliary inequality: k + k * (x / k) > x
  -- for all natural x and for all natural k > 0.
  have add_mul_div_self {x k : ℕ} (hk : 0 < k) : k + k * (x / k) > x := by
    rw [mul_div_self]
    suffices x % k < k by omega
    apply Nat.mod_lt _ hk
  -- Assume that 0 < a < b < c and prove that 0 < f(a, b, c) iff a = 1.
  have hf1 {a b c : ℕ} (ha0 : 0 < a) (hab : a < b) (hbc : b < c) : 0 < f a b c ↔ a = 1 := by
    rw [hf]
    constructor
    · intro h
      -- Suppose that 0 < f(a, b, c). We need to show that a = 1.
      -- 0 < f(a, b, c) implies that it is possible to find 0 < x, 0 < y, 0 < z such
      -- that all numbers in the range [1, 1000] can be written as x' * a + y' * b + z' * c
      -- with x' ≤ x, y' ≤ y, and z' ≤ z.
      apply Nat.nonempty_of_pos_sInf at h
      simp only [gt_iff_lt, mem_Icc, and_imp, Set.Nonempty.eq_1, Set.mem_setOf_eq] at h
      have ⟨n, x, y, z, hn, hx, hy, hz, hi⟩ := h
      -- In particular, we have 1 = x' * a + y' * b + z' * c.
      have ⟨x', y', z', heq, hx', hy', hz'⟩ := hi 1 (le_refl 1) (by norm_num)
      clear * - heq hab hbc ha0
      -- Suppose that a ≠ 1 and show that x' * a + y' * b + z' * c ≠ 1.
      contrapose! heq
      by_cases h1 : x' ≠ 0
      -- If x' ≠ 0 then x' * a + y' * b + z' * c ≥ x' * a ≥ a > 1 (because 0 < a and a ≠ 1).
      · apply ne_of_lt
        suffices 1 * 1 < x' * a by omega
        apply Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega) (by omega)
      by_cases h2 : y' ≠ 0
      -- If y' ≠ 0 then x' * a + y' * b + z' * c ≥ y' * b ≥ b > 1 (because 0 < a < b).
      · apply ne_of_lt
        suffices 1 * 1 < y' * b by omega
        apply Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega) (by omega)
      by_cases h3 : z' ≠ 0
      -- If z' ≠ 0 then x' * a + y' * b + z' * c ≥ z' * c ≥ c > 1 (because 0 < a < b < c).
      · apply ne_of_lt
        suffices 1 * 1 < z' * c by omega
        apply Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega) (by omega)
      -- So we get that x' = y' = z' = 0 and
      -- x' * a + y' * b + z' * c = 0 ≠ 1.
      push_neg at h1 h2 h3
      simp [h1, h2, h3]
    · intro ha
      -- Assume that a = 1 and show that 0 < f(1, b, c).
      -- Define s such that f(1, b, c) = sInf s.
      set s := {n : ℕ | _}
      -- It is enough to show that f(1, b, c) ≠ 0.
      suffices ¬ sInf s = 0 by omega
      simp only [gt_iff_lt, mem_Icc, and_imp, Nat.sInf_eq_zero, Set.mem_setOf_eq, not_or,
        not_exists, not_and, not_forall, Classical.not_imp, not_le, s]
      -- It is enough to show that 0 ∉ s and s is not empty.
      -- 0 ∉ s because s contains positive numbers only.
      refine ⟨by omega, ?_⟩
      apply Set.Nonempty.ne_empty
      -- Show that s is not empty. Demonstrate that 1002 = 1000 + 1 + 1 ∈ s.
      use 1002, 1000, 1, 1
      norm_num
      intro i hi1 hi2
      -- Clearly, all numbers i ∈ [1, 1000] can be written as i = i * 1 + 0 * b + 0 * c with
      -- i ≤ 1000 = x.
      use i, 0, 0
      simp [ha, hi2]
  -- f(1, b, c) = sInf s. Show that the set s is equal to the set of all numbers n
  -- which can be written as n = x + y + z with x, y, z > 0 such that
  -- x ≥ min(b - 1, 1000), x + b * y ≥ min(c - 1, 1000), and x + b * y + c * z ≥ 1000.
  have hs {b c} (hb : 1 < b) (hbc : b < c) : {n | ∃ x y z, n = x + y + z ∧ x > 0 ∧
              y > 0 ∧ z > 0 ∧ ∀ i ∈ Icc 1 1000, ∃ x' y' z', i = x' + y' * b + z' * c ∧ x' ≤ x ∧ y' ≤ y ∧ z' ≤ z}
      = {n | ∃ x y z, n = x + y + z ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≥ min (b - 1) 1000 ∧ x + b * y ≥ min (c - 1) 1000 ∧ x + b * y + c * z ≥ 1000} := by
    ext n
    simp only [gt_iff_lt, mem_Icc, and_imp, Set.mem_setOf_eq, ge_iff_le, tsub_le_iff_right]
    constructor
    · intro ⟨x, y, z, hn, hx, hy, hz, h⟩
      -- Suppose n ∈ s, n = x + y + z and all number i ∈ [1, 1000] can be written as
      -- i = x' + y' * b + z' * c with x' ≤ x, y' ≤ y, and z' ≤ z.
      -- We need to show that x ≥ min(b - 1, 1000), x + b * y ≥ min(c - 1, 1000), and x + b * y + c * z ≥ 1000.
      use x, y, z, hn, hx, hy, hz
      constructorm* _ ∧ _
      -- Show that x ≥ min(b - 1, 1000).
      -- Let i = min(b - 1, 1000) ∈ [1, 1000]. We can find x', y', z' such that
      -- min(b - 1, 1000) = x' + y' * b + z' * c, x' ≤ x, y' ≤ y, z' ≤ z.
      · have ⟨x', y', z', hi, hx', hy', hz'⟩ := h (min (b - 1) 1000) (by omega) (by omega)
        by_cases hy0 : y' ≠ 0
        -- Suppose that y' ≠ 0 and derive a contradiction: min(b - 1, 1000) < x' + y' * b + z' * c.
        · contrapose! hi
          apply ne_of_lt
          calc
            min (b - 1) 1000 < 1 * b := by omega
            _ ≤ y' * b := Nat.mul_le_mul (by omega) (le_refl _)
            _ ≤ x' + y' * b + z' * c := by omega
        -- Suppose that z' ≠ 0 and derive a contradiction: min(b - 1, 1000) < x' + y' * b + z' * c.
        by_cases hz0 : z' ≠ 0
        · contrapose! hi
          apply ne_of_lt
          calc
            min (b - 1) 1000 < 1 * c := by omega
            _ ≤ z' * c := Nat.mul_le_mul (by omega) (le_refl _)
            _ ≤ x' + y' * b + z' * c := by omega
        -- We have y' = 0, z' = 0, so min(b - 1, 1000) = x' ≤ x.
        push_neg at hy0 hz0
        subst y' z'
        linarith
      -- Show that x + b * y ≥ min(c - 1, 1000).
      -- Let i = min(c - 1, 1000) ∈ [1, 1000]. We can find x', y', z' such that
      -- min(c - 1, 1000) = x' + y' * b + z' * c, x' ≤ x, y' ≤ y, z' ≤ z.
      · have ⟨x', y', z', hi, hx', hy', hz'⟩ := h (min (c - 1) 1000) (by omega) (by omega)
        -- Suppose that z' ≠ 0 and derive a contradiction: min(c - 1, 1000) < x' + y' * b + z' * c.
        by_cases hz0 : z' ≠ 0
        · contrapose! hi
          apply ne_of_lt
          calc
            min (c - 1) 1000 < 1 * c := by omega
            _ ≤ z' * c := Nat.mul_le_mul (by omega) (le_refl _)
            _ ≤ x' + y' * b + z' * c := by omega
        -- We have z' = 0, so min(c - 1, 1000) = x' + y' * b ≤ x + y * b.
        push_neg at hz0
        subst z'
        nlinarith
      -- Show that x + b * y + c * z ≥ 1000.
      -- Let i = 1000 ∈ [1, 1000]. We can find x', y', z' such that
      -- 1000 = x' + y' * b + z' * c, x' ≤ x, y' ≤ y, z' ≤ z.
      -- It immediately follows that x + y * b + z * c ≥ x' + y' * b + z' * c = 1000.
      · have ⟨x', y', z', hi, hx', hy', hz'⟩ := h 1000 (by omega) (by omega)
        nlinarith
    · intro ⟨x, y, z, hn, hx, hy, hz, h1, h2, h3⟩
      -- Now suppose that min(b - 1, 1000) ≤ x, min(c - 1, 1000) ≤ x + b * y, 1000 ≤ x + b * y + c * z.
      -- Show that all numbers i ∈ [1, 1000] can be written as i = x' + b * y' + c * z' with
      -- x' ≤ x, y' ≤ y, z' ≤ z.
      use x, y, z, hn, hx, hy, hz
      intro i hi1 hi2
      -- Prove an auxiliary inequality:
      -- if 0 < t, t - 1 ≤ u, j ≤ u + t * v then j ≤ u + t * min(v, j / t).
      have ineq {j u v t : ℕ} (ht : 0 < t) (hu : t - 1 ≤ u) (huv : j ≤ u + t * v) : j ≤ u + t * min v (j / t) := by
        cases' min_choice v (j / t) with h h
        · rw [h]
          omega
        · nth_rw 1 [h, ← Nat.div_add_mod j t, add_comm]
          gcongr
          suffices j % t < t by omega
          apply Nat.mod_lt _ (by omega)
      -- If b > 1000 then the result is trivial: min(b - 1, 1000) ≤ x implies that
      -- x ≥ 1000 and all numbers i ∈ [1, 1000] can be written as
      -- i = i + b * 0 + c * 0 with i ≤ x.
      by_cases hb1 : b > 1000
      · use i, 0, 0
        omega
      replace h1 : b - 1 ≤ x := by omega
      -- Show that any number j ≤ x + b * y can be written as
      -- j = x' + b * y' with x' ≤ x and y' ≤ y.
      have h j (hj2 : j ≤ x + b * y) : ∃ x' y', j = x' + b * y' ∧ x' ≤ x ∧ y' ≤ y := by
        -- Let u = min(y, j / b).
        set u := min y (j / b)
        -- Show that x' = j - b * u and y' = u work.
        use j - b * u, u
        -- y' = u = min(y, j / b) ≤ y is easy.
        refine ⟨?_, ?_, by omega⟩
        -- Show that j = x' + b * y' = j - b * u + b * u. It is enough to show that
        -- b * u ≤ j.
        -- b * u ≤ b * (j / b) ≤ j.
        · suffices b * u ≤ j by omega
          calc
            b * u ≤ b * (j / b) := by gcongr; omega
            _ ≤ j := Nat.mul_div_le j b
        -- Show that x' = j - b * u ≤ x. It is enough to show that j ≤ x + b * u.
        · suffices j ≤ x + b * u by omega
          -- The result follows from the auxiliary inequality proved above.
          apply ineq (by omega) h1 hj2
      -- If c > 1000 then the result follows from the previous lemma:
      -- x + b * y ≥ min(1000, c) implies x + b * y ≥ 1000 and all numbers j ≤ x + b * y
      -- can be written as x' + b * y'.
      by_cases hc1 : c > 1000
      · have ⟨x', y', hi, hx', hy'⟩ := h i (by omega)
        use x', y', 0
        simp [hi, mul_comm, hx', hy']
      replace h2 : c - 1 ≤ x + b * y := by omega
      -- Let z' = min(z, i / c).
      set z' := min z (i / c)
      -- We have i ≤ x + b * y + c * z' (from the auxiliary inequality).
      have ineq2 : i ≤ x + b * y + c * z' := ineq (by omega) h2 (by omega)
      -- We have i - c * z' ≤ x + b * y so we can find x', y' such that
      -- i - c * z' = x' + b * y'.
      have ⟨x', y', hi, hx', hy'⟩ := h _ (show i - c * z' ≤ x + b * y by omega)
      use x', y', z'
      simp [hx', hy', mul_comm, ← hi]
      refine ⟨?_, by omega⟩
      -- It is left to show that i = x' + b * y' + c * z'.
      -- We have x' + b * y' = i - c * z'. So we need to show that c * z' ≤ i.
      suffices c * z' ≤ i by omega
      calc
        -- c * z' ≤ c * (i / c) ≤ i.
        c * z' ≤ c * (i / c) := by gcongr; omega
        _ ≤ i := Nat.mul_div_le _ _
  -- Derive an upper bound for f(1, b, c). Show that 1 < b < c, 0 < x, y, z,
  -- x ≥ min(b - 1, 1000), x + b * y ≥ min(c - 1, 1000), x + b * y + c * z ≥ 1000
  -- imply that f(1, b, c) ≤ x + y + z.
  have hf_upper b c x y z (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hb : 1 < b) (hbc : b < c)
      (h1 : x ≥ min (b - 1) 1000) (h2 : x + b * y ≥ min (c - 1) 1000) (h3 : x + b * y + c * z ≥ 1000) : f 1 b c ≤ x + y + z := by
    -- The result follows from the definition of f(1, b, c) = sInf s and the fact that
    -- x + y + z ∈ s when all conditions of this lemma are satisfied.
    simp_rw [hf, mul_one]
    apply Nat.sInf_le
    rw [hs hb hbc]
    simp only [gt_iff_lt, Set.mem_setOf_eq]
    use x, y, z
  -- Derive a lower bound for f(1, b, c). Assume 1 < b < c ≤ 1000.
  -- Show that if for all x, y, z > 0 we have
  -- x ≥ b - 1, x + b * y ≥ c - 1, x + b * y + c * z ≥ 1000 → x + y + z ≥ r
  -- then r ≤ f(1, b, c).
  have hf_lower r b c (hb : 1 < b) (hbc : b < c) (hc : c ≤ 1000)
      (hlower : ∀ x y z, 0 < x → 0 < y → 0 < z → x ≥ b - 1 → x + b * y ≥ c - 1 → x + b * y + c * z ≥ 1000 → x + y + z ≥ r) :
        r ≤ f 1 b c := by
    have hpos : 0 < f 1 b c := by rw [hf1 zero_lt_one hb hbc]
    simp_rw [hf, mul_one, hs hb hbc] at hpos ⊢
    clear * - hpos hb hbc hc hlower
    set s := {n | _}
    -- We have f(1, b, c) = sInf s and sInf s ∈ s because s ≠ ∅
    -- (it follows from sInf s = f(1, b, c) > 0).
    have hs : sInf s ∈ s := by
      apply Nat.sInf_mem
      apply Nat.nonempty_of_pos_sInf hpos
    -- Let v = sInf s.
    set v := sInf s
    -- v ∈ s implies that v = x + y + z with x, y, z > 0 and x ≥ b - 1, x + b * y ≥ c - 1,
    -- x + b * y + c * z ≥ 1000.
    simp only [gt_iff_lt, ge_iff_le, tsub_le_iff_right, Set.mem_setOf_eq, s] at hs
    -- By our assumption, x + y + z ≥ r, so f(1, b, c) = sInf s = v = x + y + z ≥ r.
    have ⟨x, y, z, hv, hx, hy, hz, h1, h2, h3⟩ := hs
    rw [hv]
    apply hlower x y z hx hy hz (by omega) (by omega) h3
  -- Derive a simple upper bound for f(1, b, c):
  -- show that f(1, b, c) ≤ c - 1 + 1000 / c for 1 < b < c ≤ 1000.
  have hf_upper1 {b c} (hb : 1 < b) (hbc : b < c) (hc : c ≤ 1000) : f 1 b c ≤ c - 1 + 1000 / c := by
    clear * - hf_upper hb hbc hc
    have hc1 : 0 < 1000 / c := Nat.div_pos hc (by omega)
    have hc2 : c - 2 + b * 1 + c * (1000 / c) ≥ 1000 := by
      nth_rw 2 [← Nat.div_add_mod 1000 c]
      suffices 1000 % c < c - 2 + b * 1 by omega
      apply lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
    -- The result follows directly from the general upper bound by taking
    -- x = c - 2, y = 1, z = 1000 / c and showing that
    -- x, y, z > 0, x ≥ b - 1 (c ≥ 0), x + y * b ≥ c - 1 (c - 2 + b ≥ c - 1), and
    -- x + y * b + z * c ≥ 1000 (c - 2 + b * 1 + c * (1000 / c) ≥ 1000).
    have := hf_upper b c (c - 2) 1 (1000 / c) (by omega) (by omega) hc1 hb hbc (by omega) (by omega) hc2
    omega
  -- Derive a simple lower bound for f(1, b, c):
  -- show that 1000 / c + 1 ≤ f(1, b, c).
  have hf_lower1 {b c} (hb : 1 < b) (hbc : b < c) (hc : c ≤ 1000) : 1000 / c + 1 ≤ f 1 b c := by
    clear * - hf_lower hb hbc hc
    -- It is enough to show that x + y + z ≥ 1000 / c + 1 when
    -- x, y, z > 0, x + b * y + c * z ≥ 1000.
    -- Indeed, c * (x + y + z) = c * x + c * y + c * z ≥ x + b * y + c * z ≥ 1000.
    -- So x + y + z > 1000 / c.
    apply hf_lower _ _ _ hb hbc hc
    intro x y z hx hy hz h1 h2 h3
    suffices 1000 / c < x + y + z by omega
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    calc
      1000 ≤ 1 * x + b * y + c * z := by linarith
      _ < c * x + c * y + c * z := by gcongr; omega
      _ = (x + y + z) * c := by ring
  -- Let p be the set (predicate) from the theorem statement:
  -- it contains all values of c such that f(a, b, c) = 97 for some values of a and b.
  set p : ℕ → Prop := {c | ∃ a b, 0 < a ∧ a < b ∧ b < c ∧ f a b c = 97}
  have hp_mem c : p c ↔ ∃ a b, 0 < a ∧ a < b ∧ b < c ∧ f a b c = 97 := by rfl
  -- Prove an auxiliary inequality: if n ∈ [12, 86] then n + 1000 / n ≤ 97.
  have ineq (n : ℕ) (hn1 : 12 ≤ n) (hn2 : n ≤ 86) : n + 1000 / n ≤ 97 := by
    suffices n + 1000 / n < 98 by omega
    rw [show n + 1000 / n = (n * n + 1000) / n by rw [Nat.mul_add_div (by omega)]]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    nlinarith
  -- Show that for all c ≤ 10 the predicate p(c) does not hold.
  have hnp10 {c} (hc : c ≤ 10) : ¬ p c := by
    rw [hp_mem]
    push_neg
    intro a b ha hab hbc
    -- Show that f(a, b, c) ≠ 97 for all 0 < a < b < c ≤ 10.
    by_cases ha1 : a = 1
    · rw [ha1]
      -- If a = 1 then we have
      -- 97 < 1000 / 10 ≤ 1000 / c + 1 ≤ f(1, b, c)
      -- (the last inequality follows from the lower bound for f(1, b, c)).
      apply ne_of_gt
      calc
        97 < 1000 / 10 := by norm_num
        _ ≤ 1000 / c := by gcongr <;> omega
        _ ≤ 1000 / c + 1 := by linarith
        _ ≤ f 1 b c := by
          apply hf_lower1 (by omega) hbc (by omega)
    -- If a ≠ 1 then f(a, b, c) = 0.
    · rw [← hf1 ha hab hbc] at ha1
      omega
  -- Show that p(11) holds.
  have hp11 : p 11 := by
    rw [hp_mem]
    -- Show that f(1, 7, 11) = 97.
    use 1, 7
    norm_num
    apply eq_of_le_of_le
    -- Show that f(1, 7, 11) ≤ 97.
    -- Use the general upper bound lemma with x = 6, y = 1, z = 90.
    -- x + y + z = 97 so f(1, 7, 11) ≤ 97.
    · have := hf_upper 7 11 6 1 90 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact this
    -- Show that 97 ≤ f(1, 7, 11).
    -- Use the general lower bound lemma with b = 7, c = 11 and show that
    -- x ≥ 6, x + 7 * y ≥ 10, x + 7 * y + 11 * z ≥ 1000 imply that
    -- x + y + z ≥ 97.
    · have := hf_lower 97 7 11 (by norm_num) (by norm_num) (by norm_num) (by omega)
      exact this
  -- Show that p(c) does not hold for c ∈ [12, 86].
  have hnp86 {c} (hc1 : 12 ≤ c) (hc2 : c ≤ 86) : ¬ p c := by
    rw [hp_mem]
    push_neg
    intro a b ha hab hb
    -- We need to show that f(a, b, c) ≠ 97 for 0 < a < b < c, c ∈ [12, 86].
    by_cases ha1 : a = 1
    swap
    -- If a ≠ 1 then f(a, b, c) = 0 ≠ 97.
    · rw [← hf1 ha hab hb] at ha1
      omega
    subst a
    -- If a = 1 then f(1, b, c) ≤ c - 1 + 1000 / c.
    -- We proved that c + 1000 / c ≤ 97 for c ∈ [12, 86] so
    -- f(1, b, c) ≤ c - 1 + 1000 / c < 97 for c ∈ [12, 86].
    have := hf_upper1 hab hb (by omega)
    have := ineq c hc1 hc2
    omega
  -- Show that p(87) does not hold.
  have hnp87 : ¬ p 87 := by
    rw [hp_mem]
    push_neg
    intro a b ha hab hb
    by_cases ha1 : a = 1
    swap
    -- If a ≠ 1 then f(a, b, 87) = 0 ≠ 97.
    · rw [← hf1 ha hab hb] at ha1
      omega
    subst a
    clear * - hab hb hf_upper add_mul_div_self ineq
    -- Suppose that a = 1 and consider two cases: b ≤ 41 and 41 < b < 87.
    by_cases hb1 : b ≤ 41
    · have h1 : 0 < 87 / b := Nat.div_pos (by omega) (by omega)
      have h2 : b + b * (87 / b) > 87 := add_mul_div_self (by omega)
      -- If b ≤ 41 then use the general upper bound lemma with
      -- x = b, y = 87 / b, c = 12.
      -- We get f(1, b, 87) ≤ b + 87 / b + 12.
      have h := hf_upper b 87 b (87 / b) 12 (by omega) h1 (by omega) hab hb (by omega)
                    (by omega) (by omega)
      -- b + 87 / b + 12 ≤ 41 + 43 + 12 = 96 < 97.
      suffices b + 87 / b + 12 ≤ 41 + 43 + 12 by omega
      gcongr
      suffices 87 / b < 44 by omega
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    · have h1 : 1 < 1000 / b := by
        suffices 1000 / 87 ≤ 1000 / b by omega
        gcongr
      -- If 41 < b ≤ 86, show that b - 1 + b * (1000 / b - 1) ≥ 914.
      have h2 : b - 1 + b * (1000 / b - 1) ≥ 914 := by
        zify [hab, h1]
        -- We have
        -- 914 = 1000 - 85 - 1
        --     ≤ 1000 - 1000 % b - 1 (because 1000 % b < b - 1 = 85)
        --     = b * (1000 / b) - 1
        --     = b - 1 + b * (1000 / b - 1).
        calc
          (914 : ℤ) = 1000 - 85 - 1 := by norm_num
          _ ≤ 1000 - 1000 % b - 1 := by
            gcongr
            norm_cast
            suffices 1000 % b < b by omega
            apply Nat.mod_lt _ (by omega)
          _ = b * (1000 / b) - 1 := by
            nth_rw 1 [← Int.emod_add_ediv' 1000 b]
            ring
          _ = b - 1 + b * (1000 / b - 1) := by
            ring
      -- Use the general upper bound lemma with x = b - 1, y = 1000 / b - 1, z = 1.
      have h := hf_upper b 87 (b - 1) (1000 / b - 1) 1 (by omega) (by omega) (by omega)
                    (by omega) hb (by omega) (by omega) (by omega)
      -- We get f(1, b, 87) ≤ b - 1 + 1000 / b - 1 + 1 = b - 1 + 1000 / b.
      -- We showed that b + 1000 / b ≤ 97 for b ∈ [12, 86] so
      -- b - 1 + 1000 / b < 97.
      replace ineq := ineq b (by omega) (by omega)
      omega
  -- Show that p(88) holds.
  have hp88 : p 88 := by
    rw [hp_mem]
    -- Show that f(1, 87, 88) = 97.
    use 1, 87
    norm_num
    apply eq_of_le_of_le
    -- Show that f(1, 87, 88) ≤ 97.
    -- Use the general upper bound lemma with x = 86, y = 1, z = 10.
    -- x + y + z = 97 so f(1, 87, 88) ≤ 97.
    · have := hf_upper 87 88 86 1 10 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact this
    -- Show that 97 ≤ f(1, 87, 88).
    -- Use the general lower bound lemma with b = 87, c = 88 and show that
    -- x ≥ 86, x + 87 * y ≥ 87, x + 87 * y + 88 * z ≥ 1000 imply that
    -- x + y + z ≥ 97.
    · have := hf_lower 97 87 88 (by norm_num) (by norm_num) (by norm_num) (by omega)
      exact this
  -- Show that p(89) holds.
  have hp89 : p 89 := by
    rw [hp_mem]
    -- Show that f(1, 87, 89) = 97.
    use 1, 87
    norm_num
    apply eq_of_le_of_le
    -- Show that f(1, 87, 89) ≤ 97.
    -- Use the general upper bound lemma with x = 86, y = 1, z = 10.
    -- x + y + z = 97 so f(1, 87, 89) ≤ 97.
    · have := hf_upper 87 89 86 1 10 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      exact this
    -- Show that 97 ≤ f(1, 87, 89).
    -- Use the general lower bound lemma with b = 87, c = 89 and show that
    -- x ≥ 86, x + 87 * y ≥ 88, x + 87 * y + 89 * z ≥ 1000 imply that
    -- x + y + z ≥ 97.
    · have := hf_lower 97 87 89 (by norm_num) (by norm_num) (by norm_num) (by omega)
      exact this
  clear * - hnp10 hp11 hnp86 hnp87 hp88 hp89
  -- It is enough to show that Nat.nth p 0 = 11 ∧ Nat.nth p 1 = 88 ∧ Nat.nth p 2 = 89.
  suffices Nat.nth p 0 = 11 ∧ Nat.nth p 1 = 88 ∧ Nat.nth p 2 = 89 by omega
  have hp : DecidablePred p := by
    classical
    infer_instance
  -- Show that Nat.count p 11 = 0.
  have hcount0 : Nat.count p 11 = 0 := by
    -- We need to show that p(n) does not hold for all n ≤ 10.
    -- We already proved this result.
    apply Nat.count_of_forall_not
    intro c hc
    apply hnp10 (by omega)
  -- Show that Nat.count p 88 = 1.
  have hcount1 : Nat.count p 88 = 1 := by
    -- Nat.count p 88 = Nat.count p 87 + if p 87 then 1 else 0.
    -- We proved that ¬p(87) so Nat.count p 88 = Nat.count p 87.
    rw [Nat.count_succ]
    simp [hnp87]
    -- Nat.count p 87 = Nat.count p (12 + 75) = Nat.count p 12 + Nat.count (fun k => p(12 + k)) 75.
    -- Nat.count p 12 = 1 because Nat.count p 11 = 0 and p(11).
    rw [show 87 = 12 + 75 by norm_num, Nat.count_add, Nat.count_succ]
    simp [hp11]
    -- Show that Nat.count (fun k => p(12 + k)) 75 = 0.
    suffices Nat.count (fun k => p (12 + k)) 75 = 0 by linarith
    -- It is enough to show that ¬ p(12 + k) for all k ∈ [0, 75) or
    -- ¬ p(k) for all k in [12, 86]. We already proved this result.
    apply Nat.count_of_forall_not
    intro m hm
    exact hnp86 (by linarith) (by linarith)
  -- Show that Nat.count p 89 = 2.
  have hcount2 : Nat.count p 89 = 2 := by
    -- We have Nat.count p 89 = Nat.count p 88 + if p 88 then 1 else 0.
    -- p(88) implies Nat.count p 89 = 1 + 1 = 2.
    rw [Nat.count_succ, hcount1]
    simp [hp88]
  -- Use the following lemma to finish the proof:
  -- If p(n) then Nat.nth p (Nat.count p n) = n.
  -- Nat.nth p 0 = Nat.nth p (Nat.count p 11) (since we have p(11)).
  -- Nat.nth p 1 = Nat.nth p (Nat.count p 88) (since we have p(88)).
  -- Nat.nth p 2 = Nat.nth p (Nat.count p 89) (since we have p(89)).
  simp [hcount0 ▸ Nat.nth_count hp11, hcount1 ▸ Nat.nth_count hp88, hcount2 ▸ Nat.nth_count hp89]